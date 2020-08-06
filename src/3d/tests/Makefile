3D=../3d

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

all: batch-test

batch-test:
	mkdir -p out.batch
	$(3D) --odir out.batch --batch $(wildcard *.3d)
	+$(MAKE) -C out.batch -f Makefile.basic USER_TARGET=test USER_CFLAGS=-Wno-ignored-qualifiers

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
