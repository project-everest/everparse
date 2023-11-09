# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KRMLLib is already built (and fails otherwise)

all: test
.PHONY: all

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
INCLUDE_KRML=--include $(KRMLLIB) --include $(KRMLLIB)/obj

ifndef STEEL_HOME
  STEEL_HOME=$(realpath ../../../steel)
endif

ALREADY_CACHED = --already_cached *,-CBOR,-CDDL,-COSE,-DPE.Messages
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED) --cmi --include $(STEEL_HOME)/lib/steel --include $(STEEL_HOME)/lib/steel/c --load_cmxs steel

FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS)

LOWPARSE_FILES=$(wildcard *.fst *.fsti)

.PHONY: clean
clean:
	rm -rf *.checked *.source .depend .depend.tmp out *.krml *.o

.depend: $(LOWPARSE_FILES)
	$(FSTAR) --dep full $(LOWPARSE_FILES) --extract 'krml:*,-FStar.Tactics' > $@.tmp
	mv $@.tmp $@

include .depend

.PHONY: verify-all
verify-all: $(ALL_CHECKED_FILES)

.PHONY: impl
impl: verify-all
	+$(MAKE) -C $@

.PHONY: dist
dist: verify-all
	+$(MAKE) -C $@

.PHONY: test
test: impl dist
	test $$(for f in $$(wc -l dist/out/CBOR.h) ; do echo $$f ; done | head -n 1) -eq $$(for f in $$(wc -l impl/out/CBOR.h) ; do echo $$f ; done | head -n 1)

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: %.fst-in %.fsti-in
%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
