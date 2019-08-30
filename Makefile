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

lowparse-test: lowparse
	+$(MAKE) -C tests/lowparse

quackyducky-unit-test: gen-test lowparse
	+$(MAKE) -C tests/unit

quackyducky-sample-test: quackyducky lowparse
	+$(MAKE) -C tests/sample

quackyducky-test: quackyducky-unit-test quackyducky-sample-test

test: lowparse-test quackyducky-test

clean:
	+$(MAKE) -C src/lowparse clean
	rm -rf *~ src/*~ _build src/*lexer.ml src/*parser.ml src/*parser.mli qd quackyducky.native

.PHONY: all gen verify test gen-test clean quackyducky lowparse lowparse-test quackyducky-test lowparse-fstar-test quackyducky-sample-test quackyducky-unit-test


# For F* testing purposes, cf. FStarLang/FStar@fc30456a163c749843c50ee5f86fa22de7f8ad7a

lowparse-fstar-test:
	+$(MAKE) -C src/lowparse fstar-test
