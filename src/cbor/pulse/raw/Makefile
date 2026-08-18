all: verify

EVERPARSE_SRC_PATH = $(realpath ../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../../spec) $(realpath ../../spec/raw)
ALREADY_CACHED := *,-CBOR.Pulse.Raw,-CBOR.Pulse.API,

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
