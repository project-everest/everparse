FSTAR_HOME ?= $(realpath ../../../../FStar)

ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/bin);$(OCAMLPATH)
else
  OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif
export OCAMLPATH

all: generated/FStar_Getopt.ml $(filter-out %~,$(wildcard *.ml*)) dune
	dune build

generated/FStar_Getopt.ml: $(FSTAR_HOME)/src/basic/ml/FStar_Getopt.ml
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
