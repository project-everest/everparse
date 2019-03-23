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

FSTAR_OPTIONS += --use_hints --use_two_phase_tc true --protect_top_level_axioms true

MY_FSTAR=$(FSTAR_EXE) --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN)

LOWPARSE_FILES=$(wildcard LowParse.*fst) $(wildcard LowParse.*fsti)

clean:
	rm -rf *.checked *.source LowParse.depend

LowParse.depend: $(LOWPARSE_FILES) Makefile.LowParse
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(LOWPARSE_FILES) > $@

include LowParse.depend

ALL_CHECKED_FILES=$(addsuffix .checked, $(ALL_FST_FILES))

LOWPARSE_CHECKED_FILES=$(addsuffix .checked, $(LOWPARSE_FILES))

OTHER_CHECKED_FILES=$(filter-out $(LOWPARSE_CHECKED_FILES), $(ALL_CHECKED_FILES))

verify-all: $(ALL_CHECKED_FILES)

$(LOWPARSE_CHECKED_FILES): %.checked:
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

$(OTHER_CHECKED_FILES): %.checked:
	test -f $@
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) --warn_error '@241@247' $<

.PHONY: all verify-all clean
