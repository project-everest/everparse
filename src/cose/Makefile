all: verify

EVERCBOR_SRC_PATH = $(realpath ..)
INCLUDE_PATHS += $(EVERCBOR_SRC_PATH)/cbor $(EVERCBOR_SRC_PATH)/cbor/pulse $(EVERCBOR_SRC_PATH)/cddl

include $(EVERCBOR_SRC_PATH)/pulse.Makefile

ALREADY_CACHED := *,-COSE,

include $(EVERCBOR_SRC_PATH)/common.Makefile
