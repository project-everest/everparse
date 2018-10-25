all: quackyducky

quackyducky: qd

qd: $(wildcard src/*.ml*)
	-@rm -f quackyducky.native
	ocamlbuild -I src -use-menhir -use-ocamlfind -package batteries -package hex quackyducky.native -classic-display -cflags '-warn-error +5'
	ln -sf quackyducky.native qd
	touch qd

test: qd
	-rm tests/unit/*.fst tests/unit/*.fsti || true
	./qd -odir tests/unit tests/unittests.rfc
	+$(MAKE) -C tests/unit

clean:
	rm -rf *~ src/*~ _build src/*lexer.ml src/*parser.ml src/*parser.mli qd quackyducky.native

.PHONY: all gen verify test clean quackyducky
