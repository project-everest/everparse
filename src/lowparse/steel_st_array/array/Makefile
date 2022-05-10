# This subdirectory needs F* pull request 2553

all: verify-all

ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifneq ($(.SHELLSTATUS),0)
    FSTAR_HOME=../../../../../FStar
  endif
endif
ifdef FSTAR_HOME
  FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
endif

ifndef KRML_HOME
  KRMLLIB=$(shell ocamlfind query karamel)
  ifneq ($(.SHELLSTATUS),0)
    KRML_HOME=../../../../../karamel
  endif
endif
ifdef KRML_HOME
  KRMLLIB=$(KRML_HOME)/krmllib
endif
INCLUDE_KRML=--include $(KRMLLIB) --include $(KRMLLIB)/obj

# for LowParse and LowParse.SteelST
INCLUDE_PATHS += .. ../..

# for Steel
INCLUDE_PATHS += $(FSTAR_HOME)/ulib/experimental

ALREADY_CACHED = --already_cached *,-LowParse.Steel,-LowParse.SteelST
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED)

LOWPARSE_FILES=$(wildcard LowParse.*.fst) $(wildcard LowParse.*.fsti)

clean:
	rm -rf *.checked *.source .depend .depend.tmp

.depend: $(LOWPARSE_FILES)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(LOWPARSE_FILES) > $@.tmp
	mv $@.tmp $@

include .depend

verify-all: $(ALL_CHECKED_FILES)

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
