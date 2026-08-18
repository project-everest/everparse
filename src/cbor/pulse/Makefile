all: verify

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(realpath ../spec)
ALREADY_CACHED := *,-CBOR.Pulse,

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
