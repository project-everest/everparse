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
QD_HOME?=../..
LOWPARSE_HOME=$(QD_HOME)/src/lowparse

INCLUDE_PATHS=$(LOWPARSE_HOME) $(FSTAR_HOME)/examples/layeredeffects

FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) --already_cached *,-LowParseWriters

ROOT_FILES=$(wildcard *.fst) $(wildcard *.fsti)

clean:
	rm -rf *.checked *.source .depend

.depend: $(ROOT_FILES)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(ROOT_FILES) > $@

include .depend

verify-all: $(ALL_CHECKED_FILES)

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in fstar-test

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
