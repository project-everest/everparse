all: verify

EVERPARSE_HOME = $(realpath ../../../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(realpath ../../../spec) $(realpath ../../../spec/raw) $(realpath ../../../spec/raw/everparse) $(EVERPARSE_HOME)/lib/everparse/lowparse

ALREADY_CACHED := *,-CBOR.Pulse.Raw.Format,-CBOR.Pulse.Raw.EverParse,

include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/everparse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile
