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

.PHONY: tot spec

.PHONY: all verify clean %.fst-in %.fsti-in fstar-test

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
