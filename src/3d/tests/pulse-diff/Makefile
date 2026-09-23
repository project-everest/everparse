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
# Requires mmap (see harness.c), hence POSIX only. On a tree where the Low*
# backend is no longer buildable at all (see LO_RUNTIME_H below) it skips.

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

# Is there still a Low* backend to compare against?
#
# On the fstar2 branch there is not: F*'s ulib no longer ships
# FStar.HyperStack, so neither LowParse.Low.* nor src/3d/prelude can be
# verified, `Options.get_pulse` is hardwired to true (3d.exe emits Pulse
# whether or not --pulse is passed), and the top-level Makefile has dropped
# the `3d-prelude` target accordingly. Both sides of the "differential" would
# then be the very same Pulse code, and the Low* side would not even compile:
# the generated C includes EverParse.h, and the Low* one is exactly what
# src/3d/prelude/buffer no longer produces.
#
# So key off that header. When it is absent the whole test skips itself with a
# message, the same way run_subdir.sh skips a sub-directory that only one of
# the two trees has -- rather than spending twenty minutes regenerating
# out.batch and then failing to compile it.
LO_RUNTIME_H = $(EVERPARSE_HOME)/src/3d/prelude/buffer/EverParse.h

ifeq (,$(wildcard $(LO_RUNTIME_H)))

all:
	@echo "pulse-diff: no Low* backend to compare against ($(LO_RUNTIME_H) is not built); skipping"

else

all: pulse-diff-test pulse-diff-subdirs

endif

.PHONY: all pulse-diff-test pulse-diff-subdirs clean

$(LO_DIR):
	+$(MAKE) -C $(EVERPARSE_HOME)/src/3d/tests batch-test

$(PU_DIR):
	+$(MAKE) -C $(PULSE_TESTS) pulse-batch

# The dispatch table is derived from the generated *Wrapper.h. The same driver
# has to be valid against both backends, so gen_diff.py is also handed the
# Pulse directory and checks that the two agree on every entrypoint signature
# before emitting anything.
driver.c: gen_diff.py | $(LO_DIR) $(PU_DIR)
	$(PYTHON) gen_diff.py $(LO_DIR) $@ $(PU_DIR)

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

# ------------------------------------------------------------------------
# The sub-directory tests.
#
# The .3d files under src/3d/tests/*/ exercise things the top-level batch
# does not: multi-module compilation, output types, external typedefs and
# iterators, conditional compilation, specialization, probes, and the
# error-handler macro. share/everparse/tests/3d mirrors the whole tree, so
# each one has a Pulse counterpart built from the same grammar.
#
# Each entry names the generated-C directory, relative to either tree. The
# `=` form is for the one layout that differs: the Low* side emits every
# output_types test into a single interpret.out, while the Pulse side gives
# each its own directory, so we pair the wide Low* directory against each
# narrow Pulse one in turn.
#
# Not listed, and why:
#   extern, static, funptr  the wrapper takes an opaque
#                           EVERPARSE_INPUT_STREAM_BASE instead of a byte
#                           array, so only the client can build an input;
#                           gen_diff.py skips those signatures.
#   exttype, goto_return    generation-only tests -- they compare emitted
#                           sources against a snapshot and never build a
#                           validator.
#   output_types/           its ExternVector.out needs Push(), which the test
#     ExternVector.out      supplies from a file that also carries its own
#                           main and its own error callback, so it cannot be
#                           linked against the generated driver.
SUBDIR_TESTS ?= \
  ifdefs/obj \
  ifdefs/batch_obj \
  iter/coarse/obj \
  iter/fine/obj \
  modules/obj \
  output_types/modules/obj \
  output_types/modules_batch/basic.out \
  output_types/interpret.out=output_types/TPoint.out \
  output_types/interpret.out=output_types/AnonUnion.out \
  output_types/interpret.out=output_types/AnonStruct.out \
  output_types/interpret.out=output_types/OutputBitFields.out \
  probe/obj \
  probe_error_handler_macro/obj \
  save_hashes/obj \
  specialize_tagged_union_array/obj \
  specialize_test/obj \
  specialize_test2/obj \
  specialize_test_error_handler_macro/obj \
  tcpip/interpret.out \
  use_error_handler_macro/obj

# Directories that are not built in both trees are skipped with a message
# rather than failing, so that this works in a partial build.
pulse-diff-subdirs:
	set -e ; for t in $(SUBDIR_TESTS) ; do \
	  CC='$(CC)' PYTHON='$(PYTHON)' ./run_subdir.sh $$t $(ITERS) ; \
	done

clean:
	rm -f diff_lo diff_pu driver.c corpus_*.bin trace_*.txt fuzzlog_*.txt \
	      semantics_lo.txt semantics_pu.txt
	rm -rf sub
