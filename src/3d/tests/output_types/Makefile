EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME
FSTAR_EXE ?= fstar.exe
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE)
SOURCE_FILES=TPoint.3d AnonStruct.3d AnonUnion.3d

all: interpret modules modules_batch

modules:
	+$(MAKE) -C $@

modules_batch:
	+$(MAKE) -C $@

interpret: $(SOURCE_FILES) interpret.out
	$(EVERPARSE_CMD) --batch TPoint.3d --odir interpret.out
	$(EVERPARSE_CMD) --batch AnonUnion.3d --odir interpret.out
	$(EVERPARSE_CMD) --batch AnonStruct.3d --odir interpret.out
	$(EVERPARSE_CMD) --batch ExternVector.3d --odir interpret.out
	$(EVERPARSE_CMD) --batch OutputBitFields.3d --odir interpret.out
	$(CXX) -o interpret.out/test1 -I interpret.out $(addprefix interpret.out/, AnonStruct_OutputTypes.c AnonStruct.c AnonStructWrapper.c) TestAnonStruct.cpp
	./interpret.out/test1
	$(CXX) -o interpret.out/test2 -I interpret.out $(addprefix interpret.out/, TPoint_OutputTypes.c TPoint.c TPointWrapper.c) TestTPoint.cpp
	./interpret.out/test2
	$(CC) -o interpret.out/test3 -I interpret.out -I . $(addprefix interpret.out/, ExternVector.c ExternVectorWrapper.c) ExternVectorDriver.c
	./interpret.out/test3

INCLUDES=$(EVERPARSE_HOME)/src/3d/prelude $(EVERPARSE_HOME)/src/3d/prelude/buffer $(EVERPARSE_HOME)/src/lowparse $(KRML_HOME)/krmllib/obj $(KRML_HOME)/krmllib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

%.out:
	mkdir -p $@

.PHONY: all interpret modules modules_batch
