all: verify

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(realpath ..)

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile

ALREADY_CACHED := *,-LowParse.Pulse,
OUTPUT_DIRECTORY := _output

include $(EVERPARSE_SRC_PATH)/common.Makefile
