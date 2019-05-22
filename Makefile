all: quackyducky lowparse

lowparse:
	+$(MAKE) -C src/lowparse

quackyducky: qd

qd: $(wildcard src/*.ml*)
	-@rm -f quackyducky.native
	ocamlbuild -I src -use-menhir -use-ocamlfind -package batteries -package hex quackyducky.native -classic-display -cflags '-warn-error +5'
	ln -sf quackyducky.native qd
	touch qd

gen-test: qd
	-rm tests/unit/*.fst tests/unit/*.fsti || true
	./qd -odir tests/unit tests/unittests.rfc
	./qd -low -odir tests/unit tests/bitcoin.rfc

gen-test2: qd
	-rm tests2/qdout/*.fst tests2/qdout/*.fsti || true
	./qd -low -odir tests2/qdout tests2/student.rfc

lowparse-test: lowparse
	+$(MAKE) -C tests/lowparse

quackyducky-test: gen-test lowparse
	+$(MAKE) -C tests/unit

test: lowparse-test quackyducky-test

clean:
	+$(MAKE) -C src/lowparse clean
	rm -rf *~ src/*~ _build src/*lexer.ml src/*parser.ml src/*parser.mli qd quackyducky.native

.PHONY: all gen verify test gen-test clean quackyducky lowparse lowparse-test quackyducky-test
