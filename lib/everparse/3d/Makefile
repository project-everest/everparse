all: verify

EVERPARSE_SRC_PATH := $(realpath ../../..)/src

include $(EVERPARSE_SRC_PATH)/windows.Makefile

INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse/pulse

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
