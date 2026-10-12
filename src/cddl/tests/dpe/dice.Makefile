all: verify

EVERPARSE_HOME = $(realpath ../../../..)

CACHE_DIRECTORY := _output
ifeq (,$(DICE_HOME))
  $(error "Please define DICE_HOME")
endif
INCLUDE_PATHS += $(DICE_HOME) $(DICE_HOME)/_cache
FSTAR_OPTIONS += --admit_smt_queries true
FSTAR_DEP_FILE := $(CACHE_DIRECTORY)/dice.depend
FSTAR_FILES := $(wildcard $(DICE_HOME)/dpe/*.fst $(DICE_HOME)/dpe/*.fsti)

include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile

.PHONY: all verify
