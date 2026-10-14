EVERPARSE_HOME ?= $(realpath ../../../../..)
include $(EVERPARSE_HOME)/src/windows.Makefile
export EVERPARSE_HOME
FSTAR_EXE ?= fstar.exe
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE) --api pulse
SOURCE_FILES=AA.3d BB.3d CC.3d

all: basic

basic: $(SOURCE_FILES) basic.out
	$(EVERPARSE_CMD) --batch AA.3d BB.3d CC.3d --odir basic.out --no_emit_output_types_defs --add_include \"AA_ExternalTypedefs.h\"
	$(CXX) -o basic.out/test -I . -I basic.out $(addprefix basic.out/, BB_OutputTypes.c CC_OutputTypes.c BB.c CC.c BBWrapper.c CCWrapper.c) Test.cpp
	./basic.out/test

FSTAR_EXE ?= fstar.exe


INCLUDES=$(EVERPARSE_HOME)/lib/everparse/3d $(EVERPARSE_HOME)/lib/everparse/lowparse

FSTAR_OPTIONS += $(addprefix --include , $(INCLUDES))

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

%.out:
	mkdir -p $@

.PHONY: all basic interpret
