all: verify

EVERCBOR_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(realpath ..)

include $(EVERCBOR_SRC_PATH)/pulse.Makefile
include $(EVERCBOR_SRC_PATH)/karamel.Makefile
include $(EVERCBOR_SRC_PATH)/everparse.Makefile

ALREADY_CACHED := *,-LowParse.Pulse,
OUTPUT_DIRECTORY := _output

include $(EVERCBOR_SRC_PATH)/common.Makefile
