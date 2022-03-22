ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/bin);$(OCAMLPATH)
else
  OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif
export OCAMLPATH


all:
	dune build


clean:
	rm -rf _build generated dune-project

