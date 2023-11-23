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
INCLUDE_KRML=--include $(KRMLLIB) --include $(KRMLLIB)/obj

ifndef STEEL_HOME
  STEEL_HOME=$(realpath ../../../../steel)
endif

ALREADY_CACHED = --already_cached *,-LowParse.SteelST
INCLUDE_PATHS = .. $(STEEL_HOME)/lib/steel $(STEEL_HOME)/lib/steel/c
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED) --load_cmxs steel

LOWPARSE_FILES := $(wildcard LowParse.*.fst) $(wildcard LowParse.*.fsti)

clean:
	rm -rf *.checked *.source .depend .depend.tmp

.depend: $(LOWPARSE_FILES)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(LOWPARSE_FILES) > $@.tmp
	mv $@.tmp $@

include .depend

STEEL_FUNCTOR_BASES=ArrayPtr R2LOutput L2ROutput
STEEL_FUNCTOR_FSTS=$(addsuffix .fst,$(addprefix LowParse.SteelST.,$(STEEL_FUNCTOR_BASES)))
STEEL_FUNCTOR_FSTI_CHECKEDS=$(addsuffix i.checked,$(STEEL_FUNCTOR_FSTS))

STEEL_FUNCTOR_VARIANTS=steel_array steel_c_array
.PHONY: $(STEEL_FUNCTOR_VARIANTS)

$(STEEL_FUNCTOR_VARIANTS): %: $(STEEL_FUNCTOR_FSTI_CHECKEDS) $(addprefix %/,$(STEEL_FUNCTOR_FSTS))
	+$(MAKE) -C $@

steel: $(STEEL_FUNCTOR_VARIANTS) $(ALL_CHECKED_FILES)

verify-all: steel

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in steel

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
