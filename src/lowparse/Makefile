# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KreMLib is already built (and fails otherwise)

all: verify-all

ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifneq ($(.SHELLSTATUS),0)
    FSTAR_HOME=../../../FStar
  endif
endif
ifdef FSTAR_HOME
  FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
endif

ifndef KREMLIN_HOME
  KREMLIB=$(shell ocamlfind query kremlin)
  ifneq ($(.SHELLSTATUS),0)
    KREMLIN_HOME=../../../kremlin
  endif
endif
ifdef KREMLIN_HOME
  KREMLIB=$(KREMLIN_HOME)/kremlib
endif
INCLUDE_KREMLIN=--include $(KREMLIB)

FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) --already_cached *-LowParse

LOWPARSE_FILES=$(wildcard LowParse.*.fst) $(wildcard LowParse.*.fsti)

clean:
	rm -rf *.checked *.source LowParse.depend

LowParse.depend: $(LOWPARSE_FILES)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(LOWPARSE_FILES) > $@

include LowParse.depend

verify-all: $(ALL_CHECKED_FILES)

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
