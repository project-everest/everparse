all: verify

EVERCBOR_SRC_PATH = $(realpath ../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(EVERCBOR_SRC_PATH)/lowparse
ALREADY_CACHED := *,-CBOR.Spec.Raw.Format,-CBOR.Spec.Raw.EverParse,

include $(EVERCBOR_SRC_PATH)/everparse.Makefile
include $(EVERCBOR_SRC_PATH)/common.Makefile
