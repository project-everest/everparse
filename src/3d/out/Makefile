FSTAR_HOME?=../../../../FStar
KREMLIN_HOME?=../../../../kremlin
OTHERFLAGS?=
EVERPARSE_HOME=../../..

all: codegen

include ../Makefile
#ROOT=Example.fst
FSTAR=$(FSTAR_HOME)/bin/fstar.exe --include ../prelude $(FSTAR_OPTIONS) $(OTHERFLAGS) --z3rlimit_factor 8 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100'
HEADERS = $(addprefix -add-include ,'"kremlin/internal/compat.h"')
KREMLIN = $(KREMLIN_HOME)/krml \
	 -ccopt "-Ofast" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out \
	 -bundle 'LowParse.\*' \
	 $(HEADERS) \
	 $(KRML_FLAGS) \
	 -warn-error -9

.dep:
	$(FSTAR) --dep full $(ROOT) --already_cached ' +LowStar +FStar +LowParse' --extract '* -Prims' > .dep

include .dep

codegen: $(ALL_KRML_FILES)
	$(KREMLIN) -skip-linking $^ $(subst .fst,,$(ROOT))_wrapper.c

kremlin: $(ALL_KRML_FILES)

%.checked:
	$(FSTAR) $< --cache_checked_modules

%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: all codegen kremlin
