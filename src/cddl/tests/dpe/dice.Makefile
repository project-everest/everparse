all: verify

EVERPARSE_SRC_PATH = $(realpath ../../..)

CACHE_DIRECTORY := _output
ifeq (,$(DICE_HOME))
DICE_HOME := $(realpath $(EVERPARSE_SRC_PATH)/../)/opt/FStar/pulse/share/pulse/examples/dice
endif
INCLUDE_PATHS += $(DICE_HOME) $(DICE_HOME)/_cache
FSTAR_OPTIONS += --admit_smt_queries true
FSTAR_DEP_FILE := $(CACHE_DIRECTORY)/dice.depend
FSTAR_FILES := $(wildcard $(DICE_HOME)/dpe/*.fst $(DICE_HOME)/dpe/*.fsti)

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

.PHONY: all verify
