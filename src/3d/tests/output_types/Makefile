EVERPARSE_HOME ?= $(realpath ../../../..)
export EVERPARSE_HOME
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe
SOURCE_FILES=TPoint.3d AnonStruct.3d AnonUnion.3d

all: basic interpret modules modules_batch

modules:
	+$(MAKE) -C $@

modules_batch:
	+$(MAKE) -C $@

basic: $(SOURCE_FILES) basic.out
	$(EVERPARSE_CMD) --batch TPoint.3d --odir basic.out
	$(EVERPARSE_CMD) --batch AnonUnion.3d --odir basic.out
	$(EVERPARSE_CMD) --batch AnonStruct.3d --odir basic.out
	$(EVERPARSE_CMD) --batch ExternVector.3d --odir basic.out
	$(EVERPARSE_CMD) --batch OutputBitFields.3d --odir basic.out
	g++ -o basic.out/test1 -I basic.out $(addprefix basic.out/, AnonStruct_OutputTypes.c AnonStruct.c AnonStructWrapper.c) TestAnonStruct.cpp
	./basic.out/test1
	g++ -o basic.out/test2 -I basic.out $(addprefix basic.out/, TPoint_OutputTypes.c TPoint.c TPointWrapper.c) TestTPoint.cpp
	./basic.out/test2
	gcc -o basic.out/test3 -I basic.out -I . $(addprefix basic.out/, ExternVector.c ExternVectorWrapper.c) ExternVectorDriver.c
	./basic.out/test3

interpret: $(SOURCE_FILES) interpret.out
	$(EVERPARSE_CMD) --batch TPoint.3d --odir interpret.out
	$(EVERPARSE_CMD) --batch AnonUnion.3d --odir interpret.out
	$(EVERPARSE_CMD) --batch AnonStruct.3d --odir interpret.out
	$(EVERPARSE_CMD) --batch ExternVector.3d --odir interpret.out
	$(EVERPARSE_CMD) --batch OutputBitFields.3d --odir interpret.out
	g++ -o interpret.out/test1 -I interpret.out $(addprefix interpret.out/, AnonStruct_OutputTypes.c AnonStruct.c AnonStructWrapper.c) TestAnonStruct.cpp
	./interpret.out/test1
	g++ -o interpret.out/test2 -I interpret.out $(addprefix interpret.out/, TPoint_OutputTypes.c TPoint.c TPointWrapper.c) TestTPoint.cpp
	./interpret.out/test2
	gcc -o interpret.out/test3 -I interpret.out -I . $(addprefix interpret.out/, ExternVector.c ExternVectorWrapper.c) ExternVectorDriver.c
	./interpret.out/test3

ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifeq ($(FSTAR_EXE),)
    # fstar.exe not found in PATH, assuming Everest source tree
    FSTAR_HOME=$(realpath $(EVERPARSE_HOME)/../FStar)
  else
    # fstar.exe found in PATH, assuming directory ending with /bin
    FSTAR_HOME=$(realpath $(dir $(FSTAR_EXE))/..)
  endif
  export FSTAR_HOME
endif

INCLUDES=$(EVERPARSE_HOME)/src/3d/prelude $(EVERPARSE_HOME)/src/3d/prelude/buffer $(EVERPARSE_HOME)/src/lowparse $(KRML_HOME)/krmllib/obj $(KRML_HOME)/krmllib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

%.out:
	mkdir -p $@

.PHONY: all basic interpret modules modules_batch
