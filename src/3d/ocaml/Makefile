FSTAR_HOME ?= $(realpath ../../../../FStar)

Main.native: FStar_Getopt.ml
	rm -f Main.native
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlbuild -tag debug -use-menhir -tag thread -use-ocamlfind -quiet -pkg batteries -pkg menhirLib -pkg fstarlib -pkg process -pkg hacl-star -pkg yojson -cflags -w,-8 Main.native

FStar_Getopt.ml: $(FSTAR_HOME)/src/basic/ml/FStar_Getopt.ml
	cp $^ $@

clean:
	rm -rf _build Main.native *~

#ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg menhirLib -pkg sedlex testlex.native
