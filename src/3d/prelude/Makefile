all: verify buffer extern

EVERPARSE_HOME := $(realpath ../../..)
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m $(EVERPARSE_HOME))
endif

FSTAR_EXE ?= fstar.exe

OTHERFLAGS?=

EVERPARSE_SRC_PATH := $(EVERPARSE_HOME)/src
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

FSTAR_OPTIONS += --ext optimize_let_vc --include $(EVERPARSE_HOME)/src/lowparse --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=10'
#--z3cliopt 'smt.arith.nl=false' --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped
FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS)

ROOT=$(wildcard *.fst) $(wildcard *.fsti)
ALREADY_CACHED=--already_cached '+Prims +LowStar +FStar +LowParse +C +Spec.Loops'

.depend: $(ROOT)
	$(FSTAR) --dep full $(ROOT) $(ALREADY_CACHED) --extract 'krml:*,-Prims,-EverParse3d.Interpreter,-FStar.Tactics' --output_deps_to $@

ifeq (,$(filter clean clean-buffer clean-extern,$(MAKECMDGOALS)))
include .depend
endif

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
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml --extract_module $(basename $(notdir $(subst .checked,,$<)))
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
