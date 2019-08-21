test.native: ast.ml parser.mly test.ml
	rm -f test.native
	ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg batteries -pkg menhirLib $@

clean:
	rm -rf _build test.native *~

#ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg menhirLib -pkg sedlex testlex.native
