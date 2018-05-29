all: quackyducky

quackyducky:
	-@rm -f quackyducky.native
	ocamlbuild -I src -use-menhir -use-ocamlfind -package batteries -package hex quackyducky.native -classic-display
	ln -sf quackyducky.native qd

out:
	mkdir out
	cp Makefile.qd out/Makefile

gen: out quackyducky
	./qd -prefix "QD.Parse_" -odir out extractrfc/tls13_draft28.rfc

verify: gen
	$(MAKE) -C out verify

test: gen
	$(MAKE) -C out test

clean:
	rm -rf *~ src/*~ _build src/*lexer.ml src/*parser.ml src/*parser.mli qd quackyducky.native out
