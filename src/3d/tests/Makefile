3D=../3d

INCLUDES=../prelude ../../lowparse ../../../../kremlin/kremlib/obj ../../../../kremlin/kremlib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

all: batch-test

batch-test:
	mkdir -p out.batch
	$(3D) --odir out.batch --batch $(wildcard *.3d)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
