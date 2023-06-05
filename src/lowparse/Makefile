# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KRMLLib is already built (and fails otherwise)

all: verify-all

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

ALREADY_CACHED = --already_cached *,-LowParse
FSTAR_OPTIONS += --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) $(ALREADY_CACHED)
ifneq (,$(STEEL_HOME))
FSTAR_OPTIONS += --include $(STEEL_HOME)/lib/steel --include $(STEEL_HOME)/lib/steel/c --load_cmxs steel
endif

LOWPARSE_FILES := $(wildcard LowParse.*.fst) $(wildcard LowParse.*.fsti)

ifeq (,$(STEEL_HOME))
LOWPARSE_FILES := $(filter-out LowParse.Steel%,$(LOWPARSE_FILES))
endif

clean:
	rm -rf *.checked *.source .depend .depend.tmp

.depend: $(LOWPARSE_FILES)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(LOWPARSE_FILES) > $@.tmp
	mv $@.tmp $@

include .depend

ifeq (,$(STEEL_HOME))
steel:
else

STEEL_FUNCTOR_BASES=ArrayPtr R2LOutput
STEEL_FUNCTOR_FSTS=$(addsuffix .fst,$(addprefix LowParse.SteelST.,$(STEEL_FUNCTOR_BASES)))
STEEL_FUNCTOR_FSTI_CHECKEDS=$(addsuffix i.checked,$(STEEL_FUNCTOR_FSTS))

STEEL_FUNCTOR_VARIANTS=steel_array steel_c_array
.PHONY: $(STEEL_FUNCTOR_VARIANTS)

$(STEEL_FUNCTOR_VARIANTS): %: $(STEEL_FUNCTOR_FSTI_CHECKEDS) $(addprefix %/,$(STEEL_FUNCTOR_FSTS))
	+$(MAKE) -C $@

steel: $(STEEL_FUNCTOR_VARIANTS) $(filter LowParse.Steel%,$(ALL_CHECKED_FILES))

endif

lowparse: steel $(ALL_CHECKED_FILES)

verify-all: lowparse

tot: $(filter LowParse.Tot.%,$(ALL_CHECKED_FILES))

spec: $(filter LowParse.Spec.%,$(ALL_CHECKED_FILES))

slow: $(filter LowParse.SLow.%,$(ALL_CHECKED_FILES))

low: $(filter LowParse.Low.%,$(ALL_CHECKED_FILES))

.PHONY: tot spec slow low

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

.PHONY: all verify-all clean %.fst-in %.fsti-in fstar-test lowparse spec steel

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)


# For F* testing purposes, cf. FStarLang/FStar@fc30456a163c749843c50ee5f86fa22de7f8ad7a

FSTAR_TEST_FILES= LowParse.Bytes.fst LowParse.Bytes32.fst		  \
	     LowParse.Spec.Base.fst LowParse.SLow.Base.fst	  \
	     LowParse.Spec.Combinators.fst			  \
	     LowParse.SLow.Combinators.fst LowParse.Spec.Enum.fst \
	     LowParse.SLow.Enum.fst

FSTAR_TEST_CHECKED_FILES=$(addsuffix .checked, $(FSTAR_TEST_FILES))

fstar-test: $(FSTAR_TEST_CHECKED_FILES)
