QD_HOME ?= $(realpath ../../..)
export QD_HOME

3D=$(QD_HOME)/bin/3d.exe

KREMLIN_HOME ?= $(realpath ../../../../kremlin)
export KREMLIN_HOME

FSTAR_HOME ?= $(realpath ../../../../FStar)
export FSTAR_HOME

INCLUDES=$(QD_HOME)/src/3d/prelude $(QD_HOME)/src/3d/prelude/buffer $(QD_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib/obj $(KREMLIN_HOME)/kremlib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

positive_tests=$(filter-out $(wildcard FAIL*.3d) FieldDependence0.3d ActAndCheck.3d,$(wildcard *.3d))
positive_tests_nosuffix=$(basename $(positive_tests))
modules_or_wrappers=$(positive_tests_nosuffix) $(addsuffix Wrapper,$(positive_tests_nosuffix))
modules_static_assertions=TestFieldPtrStaticAssertions.c AlignStaticAssertions.c
clean_out_files=$(addsuffix .c,$(modules_or_wrappers)) $(modules_static_assertions) $(addsuffix .h,$(modules_or_wrappers))
OTHER_HEADERS=TestFieldPtrBase.h AlignC.h

all: batch-test batch-test-negative batch-cleanup-test inplace-hash-test modules tcpip extern output-types batch-interpret-test modules-interpret

INTERPRETABLE_FILES=$(filter-out FAILNoEntrypoint.3d, $(wildcard *.3d))
INTERPRETABLE_MODULES=$(basename $(INTERPRETABLE_FILES))
interpret_all: $(addsuffix .interpret, $(INTERPRETABLE_MODULES))

extern:
	+$(MAKE) -C extern

modules:
	+$(MAKE) -C modules

modules-interpret:
	+$(MAKE) -C modules-interpret

tcpip:
	+$(MAKE) -C tcpip

output-types:
	+$(MAKE) -C output_types

batch-test-negative: $(addsuffix .negtest,$(wildcard FAIL*.3d))

%.3d.negtest: %.3d
	mkdir -p out.fail.batch
	! $(3D) --odir out.fail.batch --batch $<

batch-test:
	mkdir -p out.batch
	$(3D) --odir out.batch --batch --no_copy_everparse_h --save_hashes $(positive_tests)
	$(3D) --odir out.batch --batch --check_hashes strong $(positive_tests)

batch-interpret-test:
	mkdir -p out.batch-interpret
	$(3D) --odir out.batch-interpret --batch --no_copy_everparse_h --save_hashes $(INTERPRETABLE_FILES)
	$(3D) --odir out.batch-interpret --batch --check_hashes strong $(INTERPRETABLE_FILES)
	cp $(OTHER_HEADERS) out.batch-interpret
	+$(MAKE) -C out.batch-interpret -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers -I $(QD_HOME)/src/3d -I $(QD_HOME)/src/3d/prelude/buffer'
	$(CXX) -o test-cpp.exe -I out.batch-interpret -I $(QD_HOME)/src/3d -I $(QD_HOME)/src/3d/prelude/buffer test.cpp out.batch-interpret/ArithmeticWrapper.o out.batch-interpret/Arithmetic.o
	./test-cpp.exe


inplace-hash-test:
	mkdir -p out.inplace-hash
	$(3D) --odir out.inplace-hash --batch --no_copy_everparse_h Comments.3d
	$(3D) --odir out.inplace-hash --batch --check_hashes inplace Comments.3d
	$(3D) --check_inplace_hash Comments.3d=out.inplace-hash/Comments.h

batch-cleanup-test:
	mkdir -p out.cleanup
	env EVERPARSE_FSTAR_OPTIONS='--admit_smt_queries true' $(3D) --odir out.cleanup --batch --cleanup --skip_c_makefiles --no_copy_everparse_h $(positive_tests)
	test "$$(ls out.cleanup | sort)" = "$$(for f in $(clean_out_files) ; do echo $$f ; done | sort)"

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

%.interpret: %.3d
	$(3D) --batch $^

clean:
	rm -rf out.batch out.fail.batch out.cleanup out.inplace-hash test-cpp.exe out.batch-interpret

.PHONY: all batch-test batch-test-negative %.negtest clean batch-cleanup-test inplace-hash-test modules modules-interpret tcpip extern %.interpret batch-interpret-test
