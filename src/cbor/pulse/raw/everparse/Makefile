all: verify

EVERCBOR_SRC_PATH = $(realpath ../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(realpath ../../../spec) $(realpath ../../../spec/raw) $(realpath ../../../spec/raw/everparse) $(EVERCBOR_SRC_PATH)/lowparse $(EVERCBOR_SRC_PATH)/lowparse/pulse

ALREADY_CACHED := *,-CBOR.Pulse.Raw.Format,-CBOR.Pulse.Raw.EverParse,

include $(EVERCBOR_SRC_PATH)/pulse.Makefile
include $(EVERCBOR_SRC_PATH)/everparse.Makefile
include $(EVERCBOR_SRC_PATH)/common.Makefile
