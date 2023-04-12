# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KRMLLib is already built (and fails otherwise)

all: verify-all extract

ifndef FSTAR_HOME
  FSTAR_EXE:=$(shell which fstar.exe)
  ifneq ($(.SHELLSTATUS),0)
    FSTAR_HOME=$(realpath ../../../FStar)
  endif
endif
ifdef FSTAR_HOME
  FSTAR_EXE:=$(FSTAR_HOME)/bin/fstar.exe
endif

ifndef KRML_HOME
  KRMLLIB:=$(shell ocamlfind query karamel)
  ifneq ($(.SHELLSTATUS),0)
    KRML_HOME=$(realpath ../../../karamel)
  endif
endif
ifdef KRML_HOME
  KRMLLIB:=$(KRML_HOME)/krmllib
endif
LOWPARSE_HOME=../lowparse
INCLUDE_KRML=--include $(KRMLLIB) --include $(KRMLLIB)/obj --include $(LOWPARSE_HOME)

ALREADY_CACHED = --already_cached *,-CBOR
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED) --cmi

ifdef STEEL_C
STEEL_C_PATH=$(FSTAR_HOME)/examples/steel/arraystructs/my_fstar
FSTAR_OPTIONS += --include $(LOWPARSE_HOME)/steel_c_array --include $(STEEL_C_PATH)/lib/steel_c --load ExtractSteelC
MY_FSTAR=$(STEEL_C_PATH)/lib/steel_c/ExtractSteelC.cmxs

$(MY_FSTAR):
	+$(MAKE) -C $(STEEL_C_PATH)

else
FSTAR_OPTIONS += --include $(LOWPARSE_HOME)/steel_array
MY_FSTAR=
endif

FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS)

LOWPARSE_FILES=$(wildcard *.fst *.fsti)

clean:
	rm -rf *.checked *.source .depend .depend.tmp out *.krml

.depend: $(LOWPARSE_FILES) $(MY_FSTAR)
	$(FSTAR) --dep full $(LOWPARSE_FILES) > $@.tmp
	mv $@.tmp $@

include .depend

lowparse: $(ALL_CHECKED_FILES)

verify-all: lowparse

%.krml:
	$(FSTAR) --codegen krml $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

KRML = $(KRML_HOME)/krml \
	 -ccopt "-Ofast" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out \
	 -bundle 'CBOR.SteelST=CBOR.\*,Steel.\*,C,LowStar.\*,LowParse.\*' \
	 -skip-linking \
	 -warn-error '@2'

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

extract: $(ALL_KRML_FILES)
	$(KRML) $(ALL_KRML_FILES)

.PHONY: all verify-all clean %.fst-in %.fsti-in lowparse extract

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
