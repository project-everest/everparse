ROOT=Main.fst
FSTAR_HOME?=../../../FStar
EVERPARSE_HOME?=../..
KREMLIN_HOME=$(EVERPARSE_HOME)/../kremlin

INCLUDE_PATHS=
OTHERFLAGS?=
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) $(addprefix --include , $(INCLUDE_PATHS))

.PHONY: ocaml

frontend: ocaml
	rm -f ocaml/Main.native
	make -C ocaml Main.native
	cp ocaml/Main.native frontend

.depend: 
	$(FSTAR) --odir ocaml --dep full $(ROOT) --extract '* -Prims -FStar' > .depend

include .depend

ocaml: $(ALL_ML_FILES)

%.checked:
	$(FSTAR) $< --cache_checked_modules

%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<))) --odir ocaml

test.native: ast.ml lexer.mll parser.mly test.ml
	rm -f test.native
	ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg batteries -pkg menhirLib $@

clean:
	rm -rf *.checked $(ALL_ML_FILES) *~


FSTAR_OPTIONS=$(OTHERFLAGS) $(addprefix --include , $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
