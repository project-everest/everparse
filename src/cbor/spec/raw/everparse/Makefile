all: verify

EVERPARSE_SRC_PATH = $(realpath ../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(EVERPARSE_SRC_PATH)/lowparse
ALREADY_CACHED := *,-CBOR.Spec.Raw.Format,-CBOR.Spec.Raw.EverParse,

include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
