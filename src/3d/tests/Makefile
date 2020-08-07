QD_HOME ?= $(realpath ../../..)
export QD_HOME

3D=$(QD_HOME)/src/3d/3d

KREMLIN_HOME ?= $(realpath ../../../../kremlin)
export KREMLIN_HOME

FSTAR_HOME ?= $(realpath ../../../../FStar)
export FSTAR_HOME

INCLUDES=$(QD_HOME)/src/3d/prelude $(QD_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib/obj $(KREMLIN_HOME)/kremlin/kremlib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

all: batch-test batch-test-negative

batch-test-negative: $(addsuffix .negtest,$(wildcard FAIL*.3d))

%.3d.negtest: %.3d
	mkdir -p out.fail.batch
	! $(3D) --odir out.fail.batch --batch $<

batch-test:
	mkdir -p out.batch
	$(3D) --odir out.batch --batch $(filter-out $(wildcard FAIL*.3d),$(wildcard *.3d))
	+$(MAKE) -C out.batch -f Makefile.basic USER_TARGET=test USER_CFLAGS=-Wno-ignored-qualifiers

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -f out.batch out.fail.batch

.PHONY: all batch-test batch-test-negative %.negtest clean
