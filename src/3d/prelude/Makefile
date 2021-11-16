all: verify buffer extern

FSTAR_HOME?=$(realpath ../../../../FStar)
KREMLIN_HOME?=$(realpath ../../../../kremlin)
OTHERFLAGS?=
EVERPARSE_HOME=../../..

FSTAR_OPTIONS=$(addprefix --include , $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj) --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=10'
#--z3cliopt 'smt.arith.nl=false' --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS) $(OTHERFLAGS) --cmi

ROOT=$(wildcard *.fst) $(wildcard *.fsti)
ALREADY_CACHED=--already_cached '+Prims +LowStar +FStar +LowParse +C +Spec.Loops'

.depend: $(ROOT)
	$(FSTAR) --dep full $(ROOT) $(ALREADY_CACHED) --extract 'Kremlin:*,-Prims,-EverParse3d.Interpreter,-EverParse3d.ProjectorTactic' > $@.tmp
	mv $@.tmp $@

include .depend

buffer: EverParse.rsp
	+$(MAKE) -C buffer

extern: EverParse.rsp
	+$(MAKE) -C extern

extract: EverParse.rsp

verify: $(ALL_CHECKED_FILES)

FILTERED_KRML_FILES=$(filter-out ResultOps.krml Actions.krml,$(ALL_KRML_FILES))

EverParse.rsp: $(FILTERED_KRML_FILES)
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

.PHONY: all clean tac_plugin buffer extract extern verify clean-buffer clean-extern

clean-buffer:
	+$(MAKE) -C buffer clean || true

clean-extern:
	+$(MAKE) -C extern clean || true

clean: clean-buffer clean-extern
	rm -f *.checked *.krml .depend *.cmi *.cmx *.cmxs *.ml *.o EverParse.rsp *.tmp .depend.tmp *~
