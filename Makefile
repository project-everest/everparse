all: quackyducky

quackyducky:
	-@rm quackyducky.native
	ocamlbuild -I src -use-menhir -use-ocamlfind -package batteries -package hex quackyducky.native -classic-display
	ln -sf quackyducky.native qd

clean:
	rm -rf *~ src/*~ _build src/*lexer.ml src/*parser.ml src/*parser.mli qd quackyducky.native
