EVERPARSE_HOME ?= $(realpath ../../../../..)
export EVERPARSE_HOME
FSTAR_EXE ?= fstar.exe
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE)
SOURCE_FILES=AA.3d BB.3d CC.3d

all: basic

basic: $(SOURCE_FILES) basic.out
	$(EVERPARSE_CMD) --batch AA.3d BB.3d CC.3d --odir basic.out --no_emit_output_types_defs --add_include \"AA_ExternalTypedefs.h\"
	$(CXX) -o basic.out/test -I . -I basic.out $(addprefix basic.out/, BB_OutputTypes.c CC_OutputTypes.c BB.c CC.c BBWrapper.c CCWrapper.c) Test.cpp
	./basic.out/test

FSTAR_EXE ?= fstar.exe

INCLUDES=$(EVERPARSE_HOME)/src/3d/prelude $(EVERPARSE_HOME)/src/3d/prelude/buffer $(EVERPARSE_HOME)/src/lowparse $(KRML_HOME)/krmllib/obj $(KRML_HOME)/krmllib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

%.out:
	mkdir -p $@

.PHONY: all basic interpret
