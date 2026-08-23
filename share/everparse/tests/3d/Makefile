# Pulse variant of src/3d/tests.
#
# Same .3d inputs, but generated against the Pulse combinator backend
# (lib/everparse/3d) with --pulse, and verified with F*.
#
# --batch runs the whole pipeline: generation, F* verification, F* extraction
# to .krml and KaRaMeL extraction to C. The generated C is then compiled.

ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../../..)
endif
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe

3D=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE) --pulse

CC ?= cc
KRML_EXE ?= $(EVERPARSE_HOME)/opt/karamel/out/bin/krml

OUT_DIR=out.pulse

# Same exclusions as src/3d/tests.
excluded_tests := FieldDependence0.3d ActAndCheck.3d

ifeq ($(OS),Windows_NT)
  # UlongToPtr is defined in Windows DLLs, conflicts with those examples
  excluded_tests += FineGrainedProbe.3d Specialize2.3d Specialize3.3d Specialize5.3d
endif

positive_tests := $(filter-out $(wildcard FAIL*.3d) $(excluded_tests),$(wildcard *.3d))
negative_tests := $(wildcard FAIL*.3d)

# Tests whose generated code does not yet survive KaRaMeL extraction under
# --pulse. They still go through generation and F* verification, but not the C
# stages. (Currently empty: all tests extract.)
no_extract_tests :=

batch_tests := $(filter-out $(no_extract_tests),$(positive_tests))
verify_only_tests := $(filter $(no_extract_tests),$(positive_tests))

VERIFY_DIR=out.pulse.verify

all: pulse-test pulse-test-negative pulse-subdirs

# Subdirectories with their own build. Only those already ported to --pulse are
# listed; the rest were copied from src/3d/tests and still drive the Low*
# backend, so building them here would prove nothing.
#
# extern and static are the ones that matter: they are the only tests that
# select an --input_stream other than buffer, so they are what exercises the
# extern and static backends, including field_ptr_after, end to end -- each
# builds a test program against a hand-written client stream and runs it.
pulse_subdirs := extern static

.PHONY: pulse-subdirs $(pulse_subdirs)
pulse-subdirs: $(pulse_subdirs)

$(pulse_subdirs):
	+$(MAKE) -C $@

.PHONY: all pulse-test pulse-test-negative pulse-batch pulse-cc pulse-verify clean clean-files

# Generation, F* verification and KaRaMeL extraction to C, in one go.
pulse-batch:
	mkdir -p $(OUT_DIR)
	$(3D) --odir $(OUT_DIR) --batch $(batch_tests)

# Compile everything KaRaMeL produced, to check the generated C is well-formed
# and that the wrappers agree with the validators' ABI.
pulse-cc: pulse-batch
	set -e ; \
	krml_include="$$($(KRML_EXE) -locate-include)" ; \
	krml_lib="$$($(KRML_EXE) -locate-krmllib)" ; \
	here="$$(pwd)" ; \
	cd $(OUT_DIR) && \
	for f in *.c ; do \
	  echo "  [CC] $$f" ; \
	  $(CC) -c -I. -I"$$here" -I"$$krml_include" -I"$$krml_lib/dist/minimal" $$f -o $${f%.c}.o ; \
	done

# The remaining tests: generation plus F* verification only.
pulse-verify:
	test -n "$(strip $(verify_only_tests))" || exit 0 ; \
	mkdir -p $(VERIFY_DIR) && \
	$(3D) --odir $(VERIFY_DIR) --no_batch --no_copy_everparse_h $(verify_only_tests)
	test -n "$(strip $(verify_only_tests))" || exit 0 ; \
	set -e ; \
	for f in $(VERIFY_DIR)/*.fsti ; do \
	  echo "  [VERIFY] $$f" ; \
	  $(3D) --odir $(VERIFY_DIR) --__micro_step verify $$f ; \
	done ; \
	for f in $(VERIFY_DIR)/*.fst ; do \
	  echo "  [VERIFY] $$f" ; \
	  $(3D) --odir $(VERIFY_DIR) --__micro_step verify $$f ; \
	done

pulse-test: pulse-cc pulse-verify

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
	rm -rf $(OUT_DIR) $(VERIFY_DIR) out.fail.pulse *.out *.err
	for d in $(pulse_subdirs) ; do $(MAKE) -C $$d clean ; done

clean: clean-files
