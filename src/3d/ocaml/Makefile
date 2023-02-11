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

all: generated/FStar_Getopt.ml $(filter-out %~,$(wildcard *.ml*)) dune
	dune build

generated/FStar_Getopt.ml: $(FSTAR_HOME)/ocaml/fstar-lib/FStar_Getopt.ml
	mkdir -p $(dir $@)
	cp $^ $@

clean-local:
	rm -rf _build *~ dune dune.tmp

clean: clean-local
	rm -rf generated

.PHONY: all clean clean-local

ifdef NO_EVERCRYPT
dune_cpp_defines=-DNO_EVERCRYPT
else
dune_cpp_defines=
endif

dune: dune.tmpl
	cpp -P $(dune_cpp_defines) < $< > $@.tmp
	mv $@.tmp $@
