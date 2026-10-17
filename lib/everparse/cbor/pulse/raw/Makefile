all: verify

EVERPARSE_HOME = $(realpath ../../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../../spec) $(realpath ../../spec/raw)
ALREADY_CACHED := *,-CBOR.Pulse.Raw,-CBOR.Pulse.API,

include $(EVERPARSE_HOME)/lib/everparse/pulse.Makefile
include $(EVERPARSE_HOME)/lib/everparse/common.Makefile
