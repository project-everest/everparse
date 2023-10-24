# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KRMLLib is already built (and fails otherwise)

all: verify-all test

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

ifeq (,$(STEEL_HOME))
	$(error "Please set STEEL_HOME to the root/prefix directory of your Steel installation.")
endif

ALREADY_CACHED = --already_cached *,-CBOR,-CDDL,-COSE,-DPE.Messages
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED) --cmi --include $(STEEL_HOME)/lib/steel --include $(STEEL_HOME)/lib/steel/c --load_cmxs steel

ifneq (,$(STEEL_C))
  FSTAR_OPTIONS += --include $(LOWPARSE_HOME)/steel_c_array
else
  FSTAR_OPTIONS += --include $(LOWPARSE_HOME)/steel_array
endif

FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS)

LOWPARSE_FILES=$(wildcard *.fst *.fsti)

clean:
	rm -rf *.checked *.source .depend .depend.tmp out *.krml *.o

.depend: $(LOWPARSE_FILES)
	$(FSTAR) --dep full $(LOWPARSE_FILES) --extract 'krml:*,-FStar.Tactics' > $@.tmp
	mv $@.tmp $@

include .depend

verify-all: $(ALL_CHECKED_FILES)

%.krml:
	$(FSTAR) --codegen krml $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

KRML = $(KRML_HOME)/krml \
	 -ccopt "-Ofast" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out \
	 -skip-linking \
	 $(KRML_OPTS) \
	 -warn-error '@2@4@15'

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

extract-steelc: $(filter-out COSE_% CDDL_% DPE_%,$(ALL_KRML_FILES))
	$(KRML) -bundle 'CBOR.SteelC+CBOR.SteelST.Raw+CBOR.Spec.Constants=CBOR.\*,Steel.\*,C,LowStar.\*,LowParse.\*[rename=CBORSteelC]' $^

extract-steel-raw: $(filter-out COSE_% CDDL_% DPE_% CBOR_SteelC% CBOR_SteelST.krml,$(ALL_KRML_FILES))
	$(KRML) -bundle 'CBOR.SteelST.Raw+CBOR.Spec.Constants=CBOR.\*,Steel.\*,C,LowStar.\*,LowParse.\*[rename=CBORRaw]' $^

extract-steel: $(filter-out COSE_% CDDL_% DPE_% CBOR_SteelC%,$(ALL_KRML_FILES))
	$(KRML) -bundle 'CBOR.SteelST+CBOR.Spec.Constants=CBOR.\*,Steel.\*,C,LowStar.\*,LowParse.\*[rename=CBOR]' $^

extract: extract-steelc extract-steel extract-steel-raw

test-steel-raw: extract-steel-raw
	$(CC) -Wall -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I $(STEEL_HOME)/include/steel -I out -c cbor_unverified.c

test-steel: extract-steel

test-steelc: extract-steelc

test: test-steel test-steelc

.PHONY: all verify-all clean %.fst-in %.fsti-in lowparse extract-steel extract-steelc extract test-steel test-steelc test extract-steel-raw test-steel-raw

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
