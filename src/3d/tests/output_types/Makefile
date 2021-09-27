QD_HOME ?= $(realpath ../../../..)
export QD_HOME
EVERPARSE_HOME=$(QD_HOME)
EVERPARSE_CMD=$(QD_HOME)/bin/3d.exe
SOURCE_FILES=TPoint.3d AnonStruct.3d AnonUnion.3d

all: $(SOURCE_FILES)
	$(EVERPARSE_CMD) --batch $^
	g++ AnonStruct_OutputTypes.c AnonStruct.c AnonStructWrapper.c TestAnonStruct.cpp
	./a.out

FSTAR_HOME ?= $(realpath ../../../../../FStar)
export FSTAR_HOME

INCLUDES=$(QD_HOME)/src/3d/prelude $(QD_HOME)/src/3d/prelude/buffer $(QD_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib/obj $(KREMLIN_HOME)/kremlib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: all
