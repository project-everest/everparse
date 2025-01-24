ROOT=Main.fst

EVERPARSE_HOME=$(realpath ../..)

FSTAR_EXE ?= fstar.exe

export KRML_HOME?=$(realpath ../../../karamel)

INCLUDE_PATHS=
OTHERFLAGS?=
FSTAR = $(FSTAR_EXE) --ext context_pruning $(OTHERFLAGS) $(addprefix --include , $(INCLUDE_PATHS) $(EVERPARSE_HOME)/src/3d/prelude) --already_cached 'Prims FStar -FStarC'

all: 3d prelude

EVERPARSE_3D=$(EVERPARSE_HOME)/bin/3d.exe
EVERPARSE_3D_MAIN=ocaml/_build/default/Main.exe

test: demo

demo: all
	+$(MAKE) -C tests

.PHONY: all prelude test clean clean-3d clean-prelude 3d

prelude:
	+$(MAKE) -C prelude

Version.fst:
	env EVERPARSE_HOME=$(EVERPARSE_HOME) ./version.sh

.depend: $(wildcard *.fst *.fsti) Version.fst
	$(FSTAR) --odir ocaml/generated --dep full $(ROOT) --extract '* -Prims -FStar' --output_deps_to .depend

include .depend

3d: $(EVERPARSE_3D)

$(EVERPARSE_3D): $(EVERPARSE_3D_MAIN)
	mkdir -p $(dir $@)
	cp $< $@
	chmod +w $@ # because dune produces read-only executables

$(EVERPARSE_3D_MAIN): $(ALL_ML_FILES) $(filter-out %~,$(wildcard ocaml/*.ml*))
	+$(MAKE) -C ocaml

%.checked:
	$(FSTAR) $< --cache_checked_modules
	touch $@

%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<))) --odir ocaml/generated

clean-prelude:
	+$(MAKE) -C prelude clean

clean-3d:
	+$(MAKE) -C ocaml clean
	rm -rf *.checked *~ Version.fst $(EVERPARSE_HOME)/bin/3d.exe

clean: clean-3d clean-prelude

FSTAR_OPTIONS=$(OTHERFLAGS) $(addprefix --include , $(EVERPARSE_HOME)/src/lowparse $(KRML_HOME)/krmllib $(KRML_HOME)/krmllib/obj)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
