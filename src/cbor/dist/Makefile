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
LOWPARSE_HOME=../../lowparse
INCLUDE_KRML=--include $(KRMLLIB) --include $(KRMLLIB)/obj

ifndef STEEL_HOME
  STEEL_HOME=$(realpath ../../../../steel)
endif
INCLUDE_PATHS=..

ALREADY_CACHED = --already_cached *,-CBOR.SteelST.Type.Def
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED) --cmi --include $(STEEL_HOME)/lib/steel --include $(STEEL_HOME)/lib/steel/c --load_cmxs steel

FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS)

LOWPARSE_FILES=$(wildcard *.fst *.fsti ../*.fst ../*.fsti)

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
	 -skip-compilation \
	 $(KRML_OPTS) \
	 -warn-error '@2@4@15'

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

extract-steel: $(filter-out COSE_% CDDL_% DPE_%,$(ALL_KRML_FILES))
	$(KRML) -bundle 'CBOR.SteelST+CBOR.Spec.Constants+CBOR.SteelST.Type.Base+CBOR.SteelST.Type.Def+CBOR.SteelST.Match+CBOR.SteelST.Type+CBOR.SteelST.Array+CBOR.SteelST.String+CBOR.SteelST.SimpleValue+CBOR.SteelST.Int64+CBOR.SteelST.Tagged+CBOR.SteelST.Map.Base+CBOR.SteelST.Map=CBOR.\*,Steel.\*,C,LowStar.\*,LowParse.\*[rename=CBOR,rename-prefix]' $^
	! test -f out/CBOR.c

extract: extract-steel

test-steel: extract-steel
	$(CC) -Wall -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic -I $(STEEL_HOME)/include/steel -I out -c cbor_test.c

test: test-steel

.PHONY: all verify-all clean %.fst-in %.fsti-in extract-steel extract test-steel test

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
