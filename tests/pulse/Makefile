all: verify

EVERPARSE_SRC_PATH = $(realpath ../../src)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse/pulse
ALREADY_CACHED := *,-ArithParse,

include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
