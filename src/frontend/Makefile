test.native: ast.ml lexer.ml parser.mly test.ml
	rm -f test.native
	ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg batteries -pkg menhirLib -pkg sedlex $@

clean:
	rm -rf _build test.native *~
