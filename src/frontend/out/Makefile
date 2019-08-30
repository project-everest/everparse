FSTAR_HOME=../../../../FStar
KREMLIN_HOME=../../../../kremlin
OTHERFLAGS?=
EVERPARSE_HOME=../../..
include ../Makefile
ROOT=Rndis.fst
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS) $(OTHERFLAGS) --z3rlimit_factor 4 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100'
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
	$(KREMLIN) -skip-compilation $^

kremlin: $(ALL_KRML_FILES)

%.checked:
	$(FSTAR) $< --cache_checked_modules

%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --extract_module $(basename $(notdir $(subst .checked,,$<)))
