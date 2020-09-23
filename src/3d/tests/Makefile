QD_HOME ?= $(realpath ../../..)
export QD_HOME

3D=$(QD_HOME)/src/3d/3d

KREMLIN_HOME ?= $(realpath ../../../../kremlin)
export KREMLIN_HOME

FSTAR_HOME ?= $(realpath ../../../../FStar)
export FSTAR_HOME

INCLUDES=$(QD_HOME)/src/3d/prelude $(QD_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib/obj $(KREMLIN_HOME)/kremlin/kremlib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

positive_tests=$(filter-out $(wildcard FAIL*.3d),$(wildcard *.3d))
positive_tests_nosuffix=$(basename $(positive_tests))
modules_or_wrappers=$(positive_tests_nosuffix) $(addsuffix Wrapper,$(positive_tests_nosuffix))
modules_static_assertions=TestFieldPtrStaticAssertions.c
clean_out_files=$(addsuffix .c,$(modules_or_wrappers)) $(modules_static_assertions) $(addsuffix .h,$(modules_or_wrappers))
OTHER_HEADERS=TestFieldPtrBase.h

all: batch-test batch-test-negative batch-cleanup-test

batch-test-negative: $(addsuffix .negtest,$(wildcard FAIL*.3d))

%.3d.negtest: %.3d
	mkdir -p out.fail.batch
	! $(3D) --odir out.fail.batch --batch $<

batch-test:
	mkdir -p out.batch
	$(3D) --odir out.batch --batch --no_copy_everparse_h $(positive_tests)
	cp $(OTHER_HEADERS) out.batch
	+$(MAKE) -C out.batch -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers -I $(QD_HOME)/src/3d'
	$(CXX) -o test-cpp.exe -I out.batch -I $(QD_HOME)/src/3d test.cpp out.batch/ArithWrapper.o out.batch/Arith.o
	./test-cpp.exe

batch-cleanup-test:
	mkdir -p out.cleanup
	env EVERPARSE_FSTAR_OPTIONS='--admit_smt_queries true' $(3D) --odir out.cleanup --batch --cleanup --skip_makefiles --no_copy_everparse_h $(positive_tests)
	test "$$(ls out.cleanup | sort)" = "$$(for f in $(clean_out_files) ; do echo $$f ; done | sort)"

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf out.batch out.fail.batch out.cleanup test-cpp.exe

.PHONY: all batch-test batch-test-negative %.negtest clean batch-cleanup-test
