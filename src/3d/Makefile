ROOT=Main.fst
FSTAR_HOME?=$(realpath ../../../FStar)
KREMLIN_HOME?=$(realpath ../../../kremlin)
EVERPARSE_HOME=../..

INCLUDE_PATHS=
OTHERFLAGS?=
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) $(addprefix --include , $(INCLUDE_PATHS) $(EVERPARSE_HOME)/src/3d/prelude) --already_cached 'Prims FStar -FStar.Getopt'

all: 3d prelude

test: demo

demo: all
	+$(MAKE) -C tests

.PHONY: all prelude test clean clean-3d clean-prelude

prelude:
	+$(MAKE) -C prelude

3d: ocaml/Main.native
	cp ocaml/Main.native 3d

Version.fst:
	env EVERPARSE_HOME=$(EVERPARSE_HOME) ./version.sh

.depend: $(wildcard *.fst *.fsti) Version.fst
	$(FSTAR) --odir ocaml/generated --dep full $(ROOT) --extract '* -Prims -FStar' > .depend

include .depend

ocaml/Main.native: $(ALL_ML_FILES) $(filter-out %~,$(wildcard ocaml/*.ml*))
	rm -f ocaml/Main.native
	+$(MAKE) -C ocaml Main.native

%.checked:
	$(FSTAR) $< --cache_checked_modules
	touch $@

%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<))) --odir ocaml/generated

clean-prelude:
	+$(MAKE) -C prelude clean

clean-3d:
	+$(MAKE) -C ocaml clean
	rm -rf *.checked *~ Version.fst

clean: clean-3d clean-prelude

FSTAR_OPTIONS=$(OTHERFLAGS) $(addprefix --include , $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
