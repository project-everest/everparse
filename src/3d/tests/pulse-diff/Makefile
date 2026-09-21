# Differential test: 3D's Low* backend vs its Pulse backend.
#
# The two backends compile the very same .3d grammars into C through completely
# different toolchains (src/3d/prelude, in Low*, vs lib/everparse/3d, in Pulse).
# They are supposed to produce parsers that behave identically. This test
# asserts exactly that, without golden files: it compiles ONE generated driver
# against BOTH backends and checks that the two executables agree, case by case,
# on
#
#   - the accept/reject verdict,
#   - every value written to an out-parameter,
#   - the full contents of every copy buffer, and
#   - every error reported to the client's <Mod>EverParseError callback,
#     including the field name.
#
# Inputs come from a feedback-guided fuzzer that uses the outcome signature as
# its progress signal: when a mutation pushes the parser one field deeper, the
# reported field name changes, so the input is kept. Both backends are fuzzed
# (each explores slightly differently) and the union of the two corpora is
# replayed through both. The fuzzer's RNG is a fixed-seed xorshift, so a given
# ITERS always produces the same corpus and this test is fully reproducible.
#
# This is how the missing `validate_pair` length-only fast path was found: it
# was the sole behavioural difference between the backends, showing up as a
# different field name (and error position) on "not enough data".
#
# Not wired into `all` on purpose: it needs BOTH backends, and the Pulse one is
# absent from NO_PULSE builds. Run it explicitly:
#
#     make -C src/3d/tests pulse-diff
#
# Requires mmap (see harness.c), hence POSIX only.

ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../../..)
endif
export EVERPARSE_HOME

CC ?= cc
PYTHON ?= python3

# Number of fuzzer iterations per entrypoint, per backend. The default is a
# compromise for CI; raise it for a deeper run.
ITERS ?= 20000

# Where each backend's generated C lives. Both are produced by the regular test
# targets, so a normal build has them already; the rules below build them on
# demand otherwise.
PULSE_TESTS := $(EVERPARSE_HOME)/share/everparse/tests/3d
LO_DIR ?= $(EVERPARSE_HOME)/src/3d/tests/out.batch
PU_DIR ?= $(PULSE_TESTS)/out.pulse

LO_INC = -I $(LO_DIR) -I $(EVERPARSE_HOME)/src/3d \
         -I $(EVERPARSE_HOME)/src/3d/prelude/buffer \
         -I $(EVERPARSE_HOME)/src/3d/tests
PU_INC = -I $(PU_DIR) -I $(PULSE_TESTS)

# -O1 keeps the build quick while still exercising the optimizer. -fwrapv and
# the feature-test macros match what the other 3D test targets use: the latter
# are what make <endian.h>'s le32toh and friends visible.
CFLAGS_COMMON = -O1 -g -std=c11 -fwrapv -D_BSD_SOURCE -D_DEFAULT_SOURCE \
                -Wno-unknown-warning-option \
                -Wno-ignored-qualifiers -Wno-unused-parameter

all: pulse-diff-test

.PHONY: all pulse-diff-test clean

$(LO_DIR):
	+$(MAKE) -C $(EVERPARSE_HOME)/src/3d/tests batch-test

$(PU_DIR):
	+$(MAKE) -C $(PULSE_TESTS) pulse-batch

# The dispatch table is derived from the generated *Wrapper.h. Both backends
# emit identical entrypoint signatures -- which this test also relies on -- so
# either directory would do; we read the Low* one and let the compiler reject
# any mismatch when the same driver is built against Pulse.
driver.c: gen_diff.py | $(LO_DIR)
	$(PYTHON) gen_diff.py $(LO_DIR) $@

diff_lo: driver.c harness.c harness.h | $(LO_DIR)
	$(CC) $(CFLAGS_COMMON) $(LO_INC) -o $@ harness.c driver.c $(LO_DIR)/*.c

diff_pu: driver.c harness.c harness.h | $(PU_DIR)
	$(CC) $(CFLAGS_COMMON) $(PU_INC) -o $@ harness.c driver.c $(PU_DIR)/*.c

corpus_lo.bin: diff_lo
	./diff_lo fuzz $@ $(ITERS) 2>fuzzlog_lo.txt

corpus_pu.bin: diff_pu
	./diff_pu fuzz $@ $(ITERS) 2>fuzzlog_pu.txt

corpus_all.bin: corpus_lo.bin corpus_pu.bin
	cat corpus_lo.bin corpus_pu.bin >$@

trace_lo.txt: diff_lo corpus_all.bin
	./diff_lo replay corpus_all.bin >$@

trace_pu.txt: diff_pu corpus_all.bin
	./diff_pu replay corpus_all.bin >$@

# The actual assertion. Reported separately so that a regression in error
# attribution alone is not mistaken for a parser-semantics regression.
pulse-diff-test: trace_lo.txt trace_pu.txt
	sed 's/|err=.*//' trace_lo.txt >semantics_lo.txt
	sed 's/|err=.*//' trace_pu.txt >semantics_pu.txt
	@if ! diff -q semantics_lo.txt semantics_pu.txt >/dev/null; then \
	  echo "FAIL: Low* and Pulse disagree on verdicts/out-params/copy-buffers"; \
	  diff semantics_lo.txt semantics_pu.txt | head -40; \
	  exit 1; \
	fi
	@if ! diff -q trace_lo.txt trace_pu.txt >/dev/null; then \
	  echo "FAIL: Low* and Pulse agree on parsing, but report different errors"; \
	  diff trace_lo.txt trace_pu.txt | head -40; \
	  exit 1; \
	fi
	@echo "pulse-diff: `wc -l <trace_lo.txt` cases, Low* and Pulse identical"

clean:
	rm -f diff_lo diff_pu driver.c corpus_*.bin trace_*.txt fuzzlog_*.txt \
	      semantics_lo.txt semantics_pu.txt
