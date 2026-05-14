all: verify

EVERPARSE_SRC_PATH = $(realpath ../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(realpath ../../../spec) $(realpath ../../../spec/raw) $(realpath ../../../spec/raw/everparse) $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

ALREADY_CACHED := *,-CBOR.Pulse.Raw.Format,-CBOR.Pulse.Raw.EverParse,-CBOR.Pulse.API.Det.Type,-CBOR.Pulse.API.Det.C,-CBOR.Pulse.API.Det.Rust,-CBOR.Pulse.API.UTF8,-CBOR.Pulse.API.Nondet.Type,-CBOR.Pulse.API.Nondet.C,-CBOR.Pulse.API.Nondet.Rust,-CBOR.Pulse.API.Det.C.Copy,

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
