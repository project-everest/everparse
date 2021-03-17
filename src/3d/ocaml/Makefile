FSTAR_HOME ?= $(realpath ../../../../FStar)

ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/bin);$(OCAMLPATH)
else
  OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif
export OCAMLPATH

Main.native: generated/FStar_Getopt.ml $(filter-out %~,$(wildcard *.ml))
	rm -f Main.native
	ocamlbuild -I generated -tag debug -use-menhir -tag thread -use-ocamlfind -quiet -pkg batteries -pkg menhirLib -pkg fstarlib -pkg process -pkg hacl-star -pkg yojson -cflags -w,-8 Main.native

generated/FStar_Getopt.ml: $(FSTAR_HOME)/src/basic/ml/FStar_Getopt.ml
	cp $^ $@

clean:
	rm -rf _build generated *~

#ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg menhirLib -pkg sedlex testlex.native
