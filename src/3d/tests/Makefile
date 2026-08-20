ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../..)
endif
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe

3D=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE)

3D_Z3_EXECUTABLE ?= z3-4.13.3

EVERPARSE_SRC_PATH := $(EVERPARSE_HOME)/src
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

# The standalone F# hash checker. Overridable, e.g. to test a Release
# build or a different runtime identifier.
HASHCHK_DIR=$(EVERPARSE_HOME)/src/3d/hashchk
HASHCHK ?= dotnet $(HASHCHK_DIR)/bin/Debug/net8.0/win-x64/everparse-hashchk.dll
export HASHCHK

INCLUDES=$(EVERPARSE_HOME)/src/3d/prelude $(EVERPARSE_HOME)/src/3d/prelude/buffer $(EVERPARSE_HOME)/src/lowparse

FSTAR_OPTIONS += $(addprefix --include , $(INCLUDES))

positive_tests:=$(filter-out $(wildcard FAIL*.3d) FieldDependence0.3d ActAndCheck.3d,$(wildcard *.3d))
ifeq ($(OS),Windows_NT)
  # UlongToPtr is defined in Windows DLLs, conflicts with those examples
  exclude_modules := FineGrainedProbe FineGrainedProbeSpecialize Specialize2 Specialize3 Specialize5 Specialize6
  positive_tests:=$(filter-out $(addsuffix .3d,$(exclude_modules)),$(positive_tests))
endif
positive_tests_nosuffix=$(basename $(positive_tests))
modules_or_wrappers=$(positive_tests_nosuffix) $(addsuffix Wrapper,$(positive_tests_nosuffix))
modules_static_assertions=$(addsuffix StaticAssertions.c, TestFieldPtr Align)
modules_auto_static_assertions=$(addsuffix AutoStaticAssertions.c, $(filter-out $(exclude_modules),Align Specialize2 Specialize3 Specialize5 Specialize6 FineGrainedProbe FineGrainedProbeSpecialize))
module_extern_apis=$(addsuffix _ExternalAPI.h, $(filter-out $(exclude_modules),Specialize2 Specialize3 Specialize5 Specialize6 FineGrainedProbe FineGrainedProbeSpecialize))
clean_out_files=\
	$(addsuffix .c,$(modules_or_wrappers)) \
	$(modules_static_assertions) \
	$(modules_auto_static_assertions) \
	$(addsuffix .h,$(modules_or_wrappers)) \
	$(module_extern_apis)

OTHER_HEADERS=TestFieldPtrBase.h AlignC.h

all: batch-test batch-test-negative batch-cleanup-test inplace-hash-test modules \
	 tcpip extern output-types batch-interpret-test elf-test static funptr ifdefs \
	 probe iter z3-testgen-test exttype z3-testgen-probe-test \
	 use_error_handler_macro \
	 check_complete \
	 save_hashes \
	 hashchk-tests

ifneq ($(OS),Windows_NT)
# Tests disabled on Windows because of UlongToPtr conflict
# probe_error_handler_macro disabled on Windows because sys/mman.h is not available
all: specialize_test specialize_test2 specialize_test_error_handler_macro specialize_tagged_union_array probe_error_handler_macro
endif

.PHONY: exttype

exttype:
	+$(MAKE) -C $@

.PHONY: iter

iter:
	+$(MAKE) -C $@

INTERPRETABLE_FILES=$(filter-out FAIL%.3d, $(wildcard *.3d))
INTERPRETABLE_MODULES=$(basename $(INTERPRETABLE_FILES))
interpret_all: $(addsuffix .interpret, $(INTERPRETABLE_MODULES))

ifdefs:
	+$(MAKE) -C ifdefs

extern:
	+$(MAKE) -C extern

static:
	+$(MAKE) -C static

funptr:
	+$(MAKE) -C funptr

modules:
	+$(MAKE) -C modules

tcpip:
	+$(MAKE) -C tcpip

output-types:
	+$(MAKE) -C output_types

.PHONY: probe
probe:
	+$(MAKE) -C $@

.PHONY: specialize_test
specialize_test:
	+$(MAKE) -C $@

.PHONY: specialize_test2
specialize_test2:
	+$(MAKE) -C $@

.PHONY: specialize_tagged_union_array
specialize_tagged_union_array:
	+$(MAKE) -C $@

.PHONY: use_error_handler_macro
use_error_handler_macro:
	+$(MAKE) -C $@

.PHONY: check_complete
check_complete:
	+$(MAKE) -C $@

.PHONY: specialize_test_error_handler_macro
specialize_test_error_handler_macro:
	+$(MAKE) -C $@

.PHONY: probe_error_handler_macro
probe_error_handler_macro:
	+$(MAKE) -C $@ 3D_Z3_EXECUTABLE=$(3D_Z3_EXECUTABLE)

.PHONY: save_hashes
save_hashes:
	+$(MAKE) -C $@

batch-test-negative: $(addsuffix .negtest,$(wildcard FAIL*.3d))

%.3d.negtest: %.3d
	mkdir -p out.fail.batch
	! $(3D) --odir out.fail.batch --batch $< >$@.out 2>$@.err

batch-test:
	mkdir -p out.batch
	$(3D) --odir out.batch --batch --no_copy_everparse_h --save_hashes $(positive_tests)
	$(3D) --odir out.batch --batch --check_hashes strong $(positive_tests)

batch-interpret-test:
	mkdir -p out.batch-interpret
	$(3D) --odir out.batch-interpret --batch --no_copy_everparse_h --save_hashes $(INTERPRETABLE_FILES)
	$(3D) --odir out.batch-interpret --batch --check_hashes strong $(INTERPRETABLE_FILES)
	cp $(OTHER_HEADERS) out.batch-interpret
	+$(MAKE) -C out.batch-interpret -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers -I $(EVERPARSE_HOME)/src/3d -I $(EVERPARSE_HOME)/src/3d/prelude/buffer'
	$(CXX) -o test-cpp.exe -I out.batch-interpret -I $(EVERPARSE_HOME)/src/3d -I $(EVERPARSE_HOME)/src/3d/prelude/buffer test.cpp out.batch-interpret/ArithmeticWrapper.o out.batch-interpret/Arithmetic.o
	./test-cpp.exe

elf-test: ELF.3d
	mkdir -p out.elf
	$(3D) --odir out.elf --batch ELF.3d
	$(CXX) -o out.elf/elf-test -I out.elf $(addprefix out.elf/, ELF.c ELFWrapper.c) TestELF.cpp

z3-testgen-test: ELF.3d
	mkdir -p out.z3-testgen
	$(3D) --z3_executable $(3D_Z3_EXECUTABLE) --batch --odir out.z3-testgen ELFTestGen.3d --z3_test ELFTestGen._ELFTestGen --z3_witnesses 10 --z3_branch_depth 5

.PHONY: z3-testgen-test

z3-testgen-probe-test: probe/src/Probe.3d
	+$(MAKE) -C probe/src

.PHONY: z3-testgen-probe-test

inplace-hash-test:
	mkdir -p out.inplace-hash
	$(3D) --odir out.inplace-hash --batch --no_copy_everparse_h Comments.3d
	$(3D) --odir out.inplace-hash --batch --check_hashes inplace Comments.3d
	$(3D) --check_inplace_hash Comments.3d=out.inplace-hash/Comments.h

##############################################################
# Same hash checks, but with the standalone F# hash checker.  #
##############################################################

# Rebuild the standalone hash checker. We use hashchk-rebuild rather
# than hashchk-boot, because 3d is already built by the time this
# Makefile is run, and rebuilding it here could race with the tests
# currently running it.
.PHONY: hashchk-boot
hashchk-boot:
	+$(MAKE) -C .. hashchk-rebuild

# Each of those rules depends on the test that generates the hashes,
# and on the hash checker, so that they can all run in parallel.

.PHONY: hashchk-batch-test
hashchk-batch-test: batch-test hashchk-boot
	$(HASHCHK) --odir out.batch --check_hashes strong $(positive_tests)

.PHONY: hashchk-batch-interpret-test
hashchk-batch-interpret-test: batch-interpret-test hashchk-boot
	$(HASHCHK) --odir out.batch-interpret --check_hashes strong $(INTERPRETABLE_FILES)

.PHONY: hashchk-inplace-hash-test
hashchk-inplace-hash-test: inplace-hash-test hashchk-boot
	$(HASHCHK) --odir out.inplace-hash --check_hashes inplace Comments.3d
	$(HASHCHK) --check_inplace_hash Comments.3d=out.inplace-hash/Comments.h

.PHONY: hashchk-save-hashes
hashchk-save-hashes: save_hashes hashchk-boot
	+$(MAKE) -C save_hashes hashchk-check

.PHONY: hashchk-modules
hashchk-modules: modules hashchk-boot
	+$(MAKE) -C modules hashchk-check

.PHONY: hashchk-tests
hashchk-tests: hashchk-batch-test hashchk-batch-interpret-test \
	 hashchk-inplace-hash-test hashchk-save-hashes hashchk-modules

echo-clean-out-files:
	echo "$$(for f in $(clean_out_files) ; do echo $$f ; done | sort)"

echo-out-files:
	echo "$$(ls out.cleanup | sort)"

test-cleanup:
	test "$$(ls out.cleanup | sort)" = "$$(for f in $(clean_out_files) ; do echo $$f ; done | sort)"

batch-cleanup-test:
	mkdir -p out.cleanup
	env EVERPARSE_FSTAR_OPTIONS='--admit_smt_queries true' $(3D) --odir out.cleanup --batch --cleanup --skip_c_makefiles --no_copy_everparse_h $(positive_tests)
	test "$$(ls out.cleanup | sort)" = "$$(for f in $(clean_out_files) ; do echo $$f ; done | sort)"

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

%.interpret: %.3d
	$(3D) --batch $^

%.clean:
	make -C $(basename $@) clean

.PHONY: %.clean

clean-files:
	rm -rf out.batch out.fail.batch out.cleanup out.elf out.inplace-hash out.pos test-cpp.exe out.batch-interpret out.z3-testgen *.out *.err

.PHONY: clean-files

clean: clean-files specialize_test.clean specialize_test2.clean probe.clean extern.clean exttype.clean funptr.clean ifdefs.clean iter/coarse.clean iter/fine.clean modules.clean output_types.clean static.clean tcpip.clean specialize_tagged_union_array.clean save_hashes.clean

clean: use_error_handler_macro.clean specialize_test_error_handler_macro.clean probe_error_handler_macro.clean check_complete.clean

.PHONY: all batch-test batch-test-negative %.negtest clean batch-cleanup-test inplace-hash-test modules tcpip extern %.interpret batch-interpret-test static funptr ifdefs
