all: tac_plugin buffer

FSTAR_HOME?=$(realpath ../../../../FStar)
KREMLIN_HOME?=$(realpath ../../../../kremlin)
OTHERFLAGS?=
EVERPARSE_HOME=../../..

FSTAR_OPTIONS=$(addprefix --include , $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj) --z3rlimit_factor 8 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100'
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS) $(OTHERFLAGS) --cmi

ROOT=$(wildcard *.fst) $(wildcard *.fsti)
ALREADY_CACHED=--already_cached '+Prims +LowStar +FStar +LowParse +C +Spec.Loops'

.depend: $(ROOT)
	$(FSTAR) --dep full $(ROOT) $(ALREADY_CACHED) --extract '* -Prims' > $@.tmp
	mv $@.tmp $@

include .depend

tac_plugin: WeakenTac.cmxs

buffer: EverParse.rsp
	+$(MAKE) -C buffer

WeakenTac.cmxs: $(ALL_CHECKED_FILES)
	$(FSTAR) --extract 'LowParse.Norm LowParse.TacLib WeakenTac' --codegen Plugin WeakenTac.fst
	env OCAMLPATH=$(FSTAR_HOME)/bin/ ocamlfind ocamlopt -w -8 -shared -package fstar-tactics-lib -o WeakenTac.cmxs LowParse_Norm.ml LowParse_TacLib.ml WeakenTac.ml

extract: EverParse.rsp

EverParse.rsp: $(ALL_KRML_FILES)
	for f in $^ ; do echo $$f ; done > $@.tmp
	mv $@.tmp $@

%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --extract_module $(basename $(notdir $(subst .checked,,$<)))
	touch $@

%.checked:
	$(FSTAR) $< --cache_checked_modules $(ALREADY_CACHED)
	touch $@

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: all clean tac_plugin buffer extract

clean:
	+$(MAKE) -C buffer clean || true
	rm -f *.checked *.krml .depend *.cmi *.cmx *.cmxs WeakenTac.ml LowParse_TacLib.ml EverParse.rsp *.tmp
