EVERPARSE_SRC_PATH ?= $(realpath ../../../../src)
LOWPARSE_PULSE_HOME ?= $(EVERPARSE_SRC_PATH)/lowparse/pulse

FSTAR_OUT_DIR ?= _output

INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse $(LOWPARSE_PULSE_HOME)

include $(EVERPARSE_SRC_PATH)/fstar.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

ALREADY_CACHED := *,-LowParseTestLib,-LowParseExample,

all: verify

.PHONY: all verify clean
