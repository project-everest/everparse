# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KRMLLib is already built (and fails otherwise)

all: verify-all

ifndef FSTAR_HOME
  FSTAR_EXE:=$(shell which fstar.exe)
  ifneq ($(.SHELLSTATUS),0)
    FSTAR_HOME=$(realpath ../../../../FStar)
  endif
endif
ifdef FSTAR_HOME
  FSTAR_EXE:=$(FSTAR_HOME)/bin/fstar.exe
endif

ifndef KRML_HOME
  KRMLLIB:=$(shell ocamlfind query karamel)
  ifneq ($(.SHELLSTATUS),0)
    KRML_HOME=$(realpath ../../../../karamel)
  endif
endif
ifdef KRML_HOME
  KRMLLIB:=$(KRML_HOME)/krmllib
endif
INCLUDE_KRML=--include $(KRMLLIB) --include $(KRMLLIB)/obj --include ..


# This list should be in sync with ../Makefile:STEEL_FUNCTOR_BASES
STEEL_FUNCTOR_BASES ?= ArrayPtr R2LOutput L2ROutput
STEEL_FUNCTOR_MODULES = $(addprefix LowParse.SteelST.,$(STEEL_FUNCTOR_BASES))
STEEL_FUNCTOR_FSTS = $(addsuffix .fst,$(STEEL_FUNCTOR_MODULES))

# Not sure if this works well. F* only expects at most 1 --already_cached. If --already_cached '*,' is moved upfront, then it will take precedence and F* will fail.
ALREADY_CACHED = $(addprefix --already_cached -,$(STEEL_FUNCTOR_MODULES)) --already_cached '*,'
# Not sure if this works on Windows, though. It fails with the fst-in trick for the Emacs mode.
# ALREADY_CACHED = --already_cached "*, $(addprefix -,$(STEEL_FUNCTOR_MODULES))"

FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED)
ifeq (,$(STEEL_HOME))
	$(error "Please set STEEL_HOME to the root/prefix directory of your Steel installation.")
endif
FSTAR_OPTIONS += --include $(STEEL_HOME)/lib/steel --include $(STEEL_HOME)/lib/steel/c --load_cmxs steel

clean:
	rm -rf *.checked *.source .depend

.depend: $(STEEL_FUNCTOR_FSTS)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(STEEL_FUNCTOR_FSTS) > $@

include .depend

lowparse: $(ALL_CHECKED_FILES)

verify-all: lowparse

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in lowparse

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
