# This subdirectory needs F* pull request 2349.

all: verify-all

ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifneq ($(.SHELLSTATUS),0)
    FSTAR_HOME=../../../../FStar
  endif
endif
ifdef FSTAR_HOME
  FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
endif

ifndef KREMLIN_HOME
  KREMLIB=$(shell ocamlfind query kremlin)
  ifneq ($(.SHELLSTATUS),0)
    KREMLIN_HOME=../../../../kremlin
  endif
endif
ifdef KREMLIN_HOME
  KREMLIB=$(KREMLIN_HOME)/kremlib
endif
INCLUDE_KREMLIN=--include $(KREMLIB) --include $(KREMLIB)/obj

# for LowParse
INCLUDE_PATHS += ..

# for Steel
INCLUDE_PATHS += $(FSTAR_HOME)/ulib/experimental

ALREADY_CACHED = --already_cached *,-LowParse.Steel
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) $(ALREADY_CACHED)

LOWPARSE_FILES=$(wildcard LowParse.*.fst) $(wildcard LowParse.*.fsti)

clean:
	rm -rf *.checked *.source .depend

.depend: $(LOWPARSE_FILES)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(LOWPARSE_FILES) > $@

include .depend

verify-all: $(ALL_CHECKED_FILES)

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
