EVERPARSE_HOME ?= $(realpath ../../../../..)
export EVERPARSE_HOME
EVERPARSE_CMD=$(EVERPARSE_HOME)/bin/3d.exe
SOURCE_FILES=AA.3d BB.3d CC.3d

all: basic

basic: $(SOURCE_FILES) basic.out
	$(EVERPARSE_CMD) --batch AA.3d BB.3d CC.3d --odir basic.out --no_emit_output_types_defs --add_include \"AA_ExternalTypedefs.h\"
	g++ -o basic.out/test -I . -I basic.out $(addprefix basic.out/, BB_OutputTypes.c CC_OutputTypes.c BB.c CC.c BBWrapper.c CCWrapper.c) Test.cpp
	./basic.out/test

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

.PHONY: all basic interpret
