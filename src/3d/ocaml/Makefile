ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifeq ($(FSTAR_EXE),)
    # fstar.exe not found in PATH, assuming Everest source tree
    FSTAR_HOME=$(realpath ../../../../FStar)
  else
    # fstar.exe found in PATH, assuming directory ending with /bin
    FSTAR_HOME=$(realpath $(dir $(FSTAR_EXE))/..)
  endif
  export FSTAR_HOME
endif

ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
else
  OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
endif
export OCAMLPATH

all: $(filter-out %~,$(wildcard *.ml*))
	dune build

clean-local:
	rm -rf _build *~

clean: clean-local
	rm -rf generated

.PHONY: all clean clean-local
