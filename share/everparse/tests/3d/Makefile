# Pulse variant of src/3d/tests.
#
# Same .3d inputs, but generated against the Pulse combinator backend
# (lib/everparse/3d) with --pulse, and verified with F*.
#
# --batch runs the whole pipeline: generation, F* verification, F* extraction
# to .krml and KaRaMeL extraction to C. The generated C is then compiled with
# -Wall -Wextra -Werror through the Makefile.basic that KaRaMeL emits, and the
# C++ driver test.cpp is linked against it and run.

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
CXX ?= c++
KRML_EXE ?= $(EVERPARSE_HOME)/opt/karamel/out/bin/krml
export KRML_EXE

OUT_DIR=out.pulse
ELF_DIR=out.elf.pulse
CLEANUP_DIR=out.cleanup.pulse
INPLACE_DIR=out.inplace-hash.pulse
Z3TESTGEN_DIR=out.z3-testgen.pulse

3D_Z3_EXECUTABLE ?= z3-4.13.3

# Same exclusions as src/3d/tests.
excluded_tests := FieldDependence0.3d ActAndCheck.3d

exclude_modules :=
ifeq ($(OS),Windows_NT)
  # UlongToPtr is defined in Windows DLLs, conflicts with those examples
  exclude_modules := FineGrainedProbe FineGrainedProbeSpecialize \
    Specialize2 Specialize3 Specialize5 Specialize6
  excluded_tests += $(addsuffix .3d,$(exclude_modules))
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

# The exact set of files --cleanup is expected to leave behind, mirroring
# src/3d/tests. Compared to the Low* backend, the Pulse backend also emits
# EverParse.c/EverParse.h and the internal/ directory, because
# EverParseErrorReasonOfResult is a real function extracted by KaRaMeL rather
# than a static inline in the hand-written prelude header.
positive_tests_nosuffix := $(basename $(positive_tests))
modules_or_wrappers := $(positive_tests_nosuffix) $(addsuffix Wrapper,$(positive_tests_nosuffix))
modules_static_assertions := $(addsuffix StaticAssertions.c, TestFieldPtr Align)
modules_auto_static_assertions := $(addsuffix AutoStaticAssertions.c, $(filter-out $(exclude_modules),Align Specialize2 Specialize3 Specialize5 Specialize6 FineGrainedProbe FineGrainedProbeSpecialize))
module_extern_apis := $(addsuffix _ExternalAPI.h, $(filter-out $(exclude_modules),Specialize2 Specialize3 Specialize5 Specialize6 FineGrainedProbe FineGrainedProbeSpecialize))
clean_out_files := \
	$(addsuffix .c,$(modules_or_wrappers)) \
	$(modules_static_assertions) \
	$(modules_auto_static_assertions) \
	$(addsuffix .h,$(modules_or_wrappers)) \
	$(module_extern_apis) \
	EverParse.c EverParse.h internal

all: pulse-test pulse-test-negative pulse-cleanup-test pulse-inplace-hash-test \
	elf-test pulse-z3-testgen-test pulse-z3-testgen-probe-test pulse-subdirs

# Subdirectories with their own build. Only those already ported to --pulse are
# listed; the rest were copied from src/3d/tests and still drive the Low*
# backend, so building them here would prove nothing.
#
# extern and static are the only tests that select an --input_stream other than
# buffer, so they are what exercises those two backends, including
# field_ptr_after, end to end -- each builds a test program against a
# hand-written client stream and runs it. modules covers multi-module input,
# output_types covers output types and their external actions, and the rest
# cover individual frontend options.
#
# probe and probe_error_handler_macro exercise probes end to end: a
# hand-written client that both copies into and repoints the copy buffer, plus
# z3 test-case generation on the same grammar.
pulse_subdirs := extern static modules output_types exttype save_hashes \
  use_error_handler_macro funptr ifdefs iter tcpip goto_return \
  specialize_test specialize_test2 specialize_test_error_handler_macro \
  specialize_tagged_union_array probe probe_error_handler_macro

.PHONY: pulse-subdirs $(pulse_subdirs)
pulse-subdirs: $(pulse_subdirs)

$(pulse_subdirs):
	+$(MAKE) -C $@

.PHONY: all pulse-test pulse-test-negative pulse-batch pulse-cc pulse-verify clean clean-files
.PHONY: pulse-cleanup-test pulse-inplace-hash-test elf-test pulse-z3-testgen-test pulse-z3-testgen-probe-test

# Generation, F* verification and KaRaMeL extraction to C, in one go, then a
# second pass checking that regenerating the sources yields the same strong
# hashes as the ones just saved.
pulse-batch:
	mkdir -p $(OUT_DIR)
	$(3D) --odir $(OUT_DIR) --batch --save_hashes $(batch_tests)
	$(3D) --odir $(OUT_DIR) --batch --check_hashes strong $(batch_tests)

# Compile everything KaRaMeL produced, to check the generated C is well-formed
# and that the wrappers agree with the validators' ABI. We go through the
# Makefile.basic that KaRaMeL emits, so that the generated code is held to the
# same -Wall -Wextra -Werror standard as in src/3d/tests. USER_TARGET=test has
# no recipe: it just forces every object to be built.
pulse-cc: pulse-batch
	+$(MAKE) -C $(OUT_DIR) -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers -I $(CURDIR)'
	$(CXX) -o test-cpp.pulse.exe -I $(OUT_DIR) test.cpp $(addprefix $(OUT_DIR)/, ArithmeticWrapper.o Arithmetic.o EverParse.o)
	./test-cpp.pulse.exe

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

# Build and link the C++ ELF test driver against the --pulse-generated ELF
# parser. As in src/3d/tests, it is not run: it needs an ELF file to read.
elf-test: ELF.3d
	mkdir -p $(ELF_DIR)
	$(3D) --odir $(ELF_DIR) --batch ELF.3d
	$(CXX) -o $(ELF_DIR)/elf-test -I $(ELF_DIR) $(addprefix $(ELF_DIR)/, ELF.c ELFWrapper.c EverParse.c) TestELF.cpp

# --cleanup must leave behind exactly the C artifacts and nothing else: no .fst,
# .checked, .krml or KaRaMeL scratch files.
pulse-cleanup-test:
	mkdir -p $(CLEANUP_DIR)
	env EVERPARSE_FSTAR_OPTIONS='--admit_smt_queries true' $(3D) --odir $(CLEANUP_DIR) --batch --cleanup --skip_c_makefiles --no_copy_everparse_h $(positive_tests)
	test "$$(ls $(CLEANUP_DIR) | sort)" = "$$(for f in $(clean_out_files) ; do echo $$f ; done | sort)"

echo-clean-out-files:
	echo "$$(for f in $(clean_out_files) ; do echo $$f ; done | sort)"

echo-out-files:
	echo "$$(ls $(CLEANUP_DIR) | sort)"

.PHONY: echo-clean-out-files echo-out-files

# The in-place hash is embedded in the generated header, so that a consumer can
# check a checked-in header against its .3d source without regenerating it.
pulse-inplace-hash-test:
	mkdir -p $(INPLACE_DIR)
	$(3D) --odir $(INPLACE_DIR) --batch Comments.3d
	$(3D) --odir $(INPLACE_DIR) --batch --check_hashes inplace Comments.3d
	$(3D) --check_inplace_hash Comments.3d=$(INPLACE_DIR)/Comments.h

# Z3-based test-case generation against the --pulse backend. The SMT half is
# backend-independent -- it runs on the InterpreterTarget AST -- so this
# exercises the generated C harness: the Pulse validators return a uint8_t
# status and report the consumed length through a size_t* position, and their
# error handler takes the input as a (base, len, pos) triple. The harness is
# compiled with -Wall -Wextra -Werror and run, and every witness must get the
# verdict Z3 predicted.
pulse-z3-testgen-test: ELF.3d
	mkdir -p $(Z3TESTGEN_DIR)
	$(3D) --z3_executable $(3D_Z3_EXECUTABLE) --batch --odir $(Z3TESTGEN_DIR) ELFTestGen.3d --z3_test ELFTestGen._ELFTestGen --z3_witnesses 10 --z3_branch_depth 5

# Same, on a grammar with probes, in both harness modes: the default one, where
# the probe callback copies from a table of witness layers, and --z3_use_ptr,
# where it repoints the copy buffer at a real address patched into the witness
# bytes at run time. The latter is what needs EVERPARSE_COPY_BUFFER_T to be an
# indirection; probe/src/Makefile drives it.
pulse-z3-testgen-probe-test: probe/src/Probe.3d
	+$(MAKE) -C probe/src

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
	rm -rf $(OUT_DIR) $(VERIFY_DIR) $(ELF_DIR) $(CLEANUP_DIR) $(INPLACE_DIR) \
	  $(Z3TESTGEN_DIR) out.fail.pulse test-cpp.pulse.exe *.out *.err
	for d in $(pulse_subdirs) ; do $(MAKE) -C $$d clean ; done

clean: clean-files
