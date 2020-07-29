all: verify extract

FSTAR_HOME?=../../../../FStar
KREMLIN_HOME?=../../../../kremlin
OTHERFLAGS?=
EVERPARSE_HOME=../../..

FSTAR_OPTIONS=$(OTHERFLAGS) $(addprefix --include , $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS) $(OTHERFLAGS) --z3rlimit_factor 8 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100' --cmi

ROOT=$(wildcard *.fst)
ALREADY_CACHED=--already_cached '+Prims +LowStar +FStar +LowParse'

.dep: $(ROOT)
	$(FSTAR) --dep full $(ROOT) $(ALREADY_CACHED) --extract '* -Prims' > .dep

include .dep

verify: $(ALL_CHECKED_FILES)

extract: $(ALL_KRML_FILES)

%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --extract_module $(basename $(notdir $(subst .checked,,$<)))

%.checked:
	$(FSTAR) $< --cache_checked_modules $(ALREADY_CACHED)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: all verify extract
