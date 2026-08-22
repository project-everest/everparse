# Pulse variant of src/3d/tests.
#
# Same .3d inputs, but generated against the Pulse combinator backend
# (lib/everparse/3d) with --pulse, and verified with F*.
#
# The C stages of src/3d/tests (KaRaMeL extraction, compiling and running the
# generated C) are not covered here: extraction of the Pulse combinators to C
# is not wired up yet. These tests therefore stop after F* verification.

ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../../..)
endif
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe

3D=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE) --pulse

OUT_DIR=out.pulse

# Same exclusions as src/3d/tests.
excluded_tests := FieldDependence0.3d ActAndCheck.3d

ifeq ($(OS),Windows_NT)
  # UlongToPtr is defined in Windows DLLs, conflicts with those examples
  excluded_tests += FineGrainedProbe.3d Specialize2.3d Specialize3.3d Specialize5.3d
endif

positive_tests := $(filter-out $(wildcard FAIL*.3d) $(excluded_tests),$(wildcard *.3d))
negative_tests := $(wildcard FAIL*.3d)

all: pulse-test pulse-test-negative

.PHONY: all pulse-test pulse-test-negative pulse-generate pulse-verify clean clean-files

# Generation only. `--no_batch` stops before KaRaMeL extraction.
pulse-generate:
	mkdir -p $(OUT_DIR)
	$(3D) --odir $(OUT_DIR) --no_batch --no_copy_everparse_h $(positive_tests)

# Verify every generated F* module. Interfaces first, then implementations,
# since an implementation needs its own interface's checked file.
pulse-verify: pulse-generate
	set -e ; \
	for f in $(OUT_DIR)/*.fsti ; do \
	  echo "  [VERIFY] $$f" ; \
	  $(3D) --odir $(OUT_DIR) --__micro_step verify $$f ; \
	done ; \
	for f in $(OUT_DIR)/*.fst ; do \
	  echo "  [VERIFY] $$f" ; \
	  $(3D) --odir $(OUT_DIR) --__micro_step verify $$f ; \
	done

pulse-test: pulse-verify

pulse-test-negative: $(addsuffix .negtest,$(negative_tests))

# A negative test must be rejected either by the 3d frontend or by F* on the
# generated code, exactly as `--batch` does for the Low* backend.
%.3d.negtest: %.3d
	mkdir -p out.fail.pulse
	! ( $(3D) --odir out.fail.pulse --no_batch $< && \
	    for f in out.fail.pulse/$*.fsti out.fail.pulse/$*.fst ; do \
	      $(3D) --odir out.fail.pulse --__micro_step verify $$f || exit 1 ; \
	    done ) >$@.out 2>$@.err

clean-files:
	rm -rf $(OUT_DIR) out.fail.pulse *.out *.err

clean: clean-files
