all: verify

EVERPARSE_HOME = $(realpath ../../..)
INCLUDE_PATHS += $(realpath ../spec)
ALREADY_CACHED := *,-CBOR.Pulse,

include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile
