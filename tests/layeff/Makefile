all: verify-all extract

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

FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN) --already_cached *,-LowParseWriters,-BUGSLowParseWriters --cmi

ROOT_FILES=$(wildcard *.fst) $(wildcard *.fsti)

HEADERS = $(addprefix -add-include ,'"kremlin/internal/compat.h"')

KREMLIN = $(KREMLIN_HOME)/krml \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -bundle 'LowParseWriters.Test=LowParse.\*,LowParseWriters,LowParseWriters.\*' \
	 $(HEADERS) \
	 -warn-error '-9@4@2'

FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS)

clean:
	rm -rf *.checked *.source .depend *.krml *.c *.h Makefile.*

.depend: $(ROOT_FILES)
	$(FSTAR) --dep full $(ROOT_FILES) > $@

include .depend

verify-all: $(ALL_CHECKED_FILES)

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR) $<
	touch $@

ALMOST_ALL_KRML_FILES := $(filter-out BUGSLowParseWriters%,$(ALL_KRML_FILES))

%.krml:
	$(FSTAR) --codegen Kremlin $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'

extract: $(ALMOST_ALL_KRML_FILES) # from .depend
	$(KREMLIN) -dast -skip-linking $^

extract-all: $(ALL_KRML_FILES) # from .depend
	$(KREMLIN) -dast -skip-linking $^


.PHONY: all verify-all clean %.fst-in %.fsti-in fstar-test extract extract-all

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
