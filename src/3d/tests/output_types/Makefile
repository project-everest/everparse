QD_HOME ?= $(realpath ../../../..)
export QD_HOME
EVERPARSE_HOME=$(QD_HOME)
EVERPARSE_CMD=$(QD_HOME)/bin/3d.exe
SOURCE_FILES=TPoint.3d AnonStruct.3d AnonUnion.3d

all: basic interpret

basic: $(SOURCE_FILES) basic.out
	$(EVERPARSE_CMD) --batch TPoint.3d --odir basic.out
	$(EVERPARSE_CMD) --batch AnonUnion.3d --odir basic.out
	$(EVERPARSE_CMD) --batch AnonStruct.3d --odir basic.out
	g++ -o basic.out/test1 -I basic.out $(addprefix basic.out/, AnonStruct_OutputTypes.c AnonStruct.c AnonStructWrapper.c) TestAnonStruct.cpp
	./basic.out/test1
	g++ -o basic.out/test2 -I basic.out $(addprefix basic.out/, TPoint_OutputTypes.c TPoint.c TPointWrapper.c) TestTPoint.cpp
	./basic.out/test2

interpret: $(SOURCE_FILES) interpret.out
	$(EVERPARSE_CMD) --batch TPoint.3d --interpret --odir interpret.out
	$(EVERPARSE_CMD) --batch AnonUnion.3d --interpret --odir interpret.out
	$(EVERPARSE_CMD) --batch AnonStruct.3d --interpret --odir interpret.out
	g++ -o interpret.out/test1 -I interpret.out $(addprefix interpret.out/, AnonStruct_OutputTypes.c AnonStruct.c AnonStructWrapper.c) TestAnonStruct.cpp
	./interpret.out/test1
	g++ -o interpret.out/test2 -I interpret.out $(addprefix interpret.out/, TPoint_OutputTypes.c TPoint.c TPointWrapper.c) TestTPoint.cpp
	./interpret.out/test2

FSTAR_HOME ?= $(realpath ../../../../../FStar)
export FSTAR_HOME

INCLUDES=$(QD_HOME)/src/3d/prelude $(QD_HOME)/src/3d/prelude/buffer $(QD_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib/obj $(KREMLIN_HOME)/kremlib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

%.out:
	mkdir -p $@

.PHONY: all basic interpret
