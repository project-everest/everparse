all: verify

EVERPARSE_SRC_PATH = $(realpath ..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl

include $(EVERPARSE_SRC_PATH)/pulse.Makefile

ALREADY_CACHED := *,-COSE,

include $(EVERPARSE_SRC_PATH)/common.Makefile
