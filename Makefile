all: quackyducky

quackyducky: qd

qd: $(wildcard src/*.ml*)
	-@rm -f quackyducky.native
	ocamlbuild -I src -use-menhir -use-ocamlfind -package batteries -package hex quackyducky.native -classic-display
	ln -sf quackyducky.native qd
	touch qd

RFC=extractrfc/tls_merged.rfc

out/Makefile: qd $(RFC)
	mkdir -p out
	./qd -prefix "QD.Parse_" -odir out $(RFC)
	cp Makefile.qd out/Makefile

gen: out/Makefile

verify: gen
	$(MAKE) -C out verify

test: gen
	$(MAKE) -C out test

clean:
	rm -rf *~ src/*~ _build src/*lexer.ml src/*parser.ml src/*parser.mli qd quackyducky.native out

.PHONY: all gen verify test clean quackyducky
