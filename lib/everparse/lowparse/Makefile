# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KRMLLib is already built (and fails otherwise)

all: verify

EVERPARSE_HOME = $(realpath ../../..)

ifeq (,$(NO_PULSE))
include $(EVERPARSE_HOME)/lib/everparse/pulse.Makefile
else
# LowParse.Pulse* and LowParse.PulseParse* are the Pulse implementation of the
# combinators; everything else here is pure specification and verifies without
# Pulse. They all sit in this one directory, so select them by module name.
FSTAR_FILES := $(filter-out LowParse.Pulse%,$(wildcard *.fst *.fsti))
endif


ALREADY_CACHED := *,-LowParse,

include $(EVERPARSE_HOME)/lib/everparse/common.Makefile

tot: $(filter LowParse.Tot.%,$(ALL_CHECKED_FILES))

spec: $(filter LowParse.Spec.%,$(ALL_CHECKED_FILES))

pulse: $(filter LowParse.Pulse%,$(ALL_CHECKED_FILES))

.PHONY: tot spec pulse

.PHONY: all verify clean %.fst-in %.fsti-in fstar-test

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)

# For F* testing purposes, cf. FStarLang/FStar@fc30456a163c749843c50ee5f86fa22de7f8ad7a

FSTAR_TEST_FILES= LowParse.Bytes.fst					  \
	     LowParse.Spec.Base.fst				  \
	     LowParse.Spec.Combinators.fst			  \
	     LowParse.Spec.Enum.fst

FSTAR_TEST_CHECKED_FILES=$(addsuffix .checked, $(FSTAR_TEST_FILES))

fstar-test: $(FSTAR_TEST_CHECKED_FILES)
