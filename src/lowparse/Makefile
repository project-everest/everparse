# This file is only to verify LowParse as a library, i.e. to place all
# LowParse.*.checked files in this directory instead of a cache. This
# is to allow users to directly pick from these .checked files instead
# of rebuilding them. This Makefile assumes that everything else from
# the F* standard library and KRMLLib is already built (and fails otherwise)

all: verify

EVERPARSE_SRC_PATH = $(realpath ..)

include $(EVERPARSE_SRC_PATH)/karamel.Makefile

ALREADY_CACHED := *,-LowParse,

include $(EVERPARSE_SRC_PATH)/common.Makefile

clean:
	rm -rf *.checked *.source .depend

tot: $(filter LowParse.Tot.%,$(ALL_CHECKED_FILES))

spec: $(filter LowParse.Spec.%,$(ALL_CHECKED_FILES))

slow: $(filter LowParse.SLow.%,$(ALL_CHECKED_FILES))

low: $(filter LowParse.Low.%,$(ALL_CHECKED_FILES))

.PHONY: tot spec slow low

.PHONY: all verify clean %.fst-in %.fsti-in fstar-test

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
