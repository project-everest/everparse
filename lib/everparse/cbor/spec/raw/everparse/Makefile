all: verify

EVERPARSE_HOME = $(realpath ../../../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(EVERPARSE_HOME)/lib/everparse/lowparse
ALREADY_CACHED := *,-CBOR.Spec.Raw.Format,-CBOR.Spec.Raw.EverParse,

include $(EVERPARSE_HOME)/src/everparse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile
