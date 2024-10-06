all: verify

EVERCBOR_SRC_PATH = $(realpath ../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../../spec) $(realpath ../../spec/raw)
ALREADY_CACHED := *,-CBOR.Pulse.Raw,-CBOR.Pulse.API,

include $(EVERCBOR_SRC_PATH)/pulse.Makefile
include $(EVERCBOR_SRC_PATH)/common.Makefile
