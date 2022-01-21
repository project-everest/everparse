all: quackyducky lowparse 3d

lowparse:
	+$(MAKE) -C src/lowparse

3d: lowparse
	+$(MAKE) -C src/3d

quackyducky: qd

qd: $(wildcard src/*.ml*)
	-@rm -f quackyducky.native
	ocamlbuild -I src -use-menhir -use-ocamlfind -package batteries -package hex quackyducky.native -classic-display -cflags '-warn-error +5+8'
	ln -sf quackyducky.native qd
	touch qd

gen-test: qd
	-rm tests/unit/*.fst tests/unit/*.fsti || true
	./qd -odir tests/unit tests/unittests.rfc
	./qd -low -odir tests/unit tests/bitcoin.rfc

lowparse-unit-test: lowparse
	+$(MAKE) -C tests/lowparse

3d-unit-test: 3d
	+$(MAKE) -C src/3d test

3d-doc-test: 3d
	+$(MAKE) -C doc 3d

3d-doc-ci: 3d
	+$(MAKE) -C doc 3d-ci

3d-ci: 3d-unit-test 3d-doc-ci

3d-test: 3d-unit-test 3d-doc-test

lowparse-bitfields-test: lowparse
	+$(MAKE) -C tests/bitfields

lowparse-test: lowparse-unit-test lowparse-bitfields-test

quackyducky-unit-test: gen-test lowparse
	+$(MAKE) -C tests/unit

quackyducky-sample-test: quackyducky lowparse
	+$(MAKE) -C tests/sample

quackyducky-test: quackyducky-unit-test quackyducky-sample-test

test: lowparse-test quackyducky-test 3d-test

ci: lowparse-test quackyducky-test 3d-ci

clean:
	+$(MAKE) -C src/3d clean
	+$(MAKE) -C src/lowparse clean
	rm -rf *~ src/*~ _build src/*lexer.ml src/*parser.ml src/*parser.mli qd quackyducky.native

.PHONY: all gen verify test gen-test clean quackyducky lowparse lowparse-test quackyducky-test lowparse-fstar-test quackyducky-sample-test quackyducky-unit-test package 3d 3d-test lowparse-unit-test lowparse-bitfields-test release everparse 3d-unit-test 3d-doc-test 3d-doc-ci 3d-ci ci

release:
	+src/package/release.sh

# Windows binary package
package:
	+src/package/package.sh -zip

# Windows binary package
package-noversion:
	+src/package/package.sh -zip-noversion

everparse:
	+src/package/package.sh -make -j 12

# For F* testing purposes, cf. FStarLang/FStar@fc30456a163c749843c50ee5f86fa22de7f8ad7a

lowparse-fstar-test:
	+$(MAKE) -C src/lowparse fstar-test
