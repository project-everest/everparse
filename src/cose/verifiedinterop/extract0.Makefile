EVERPARSE_HOME = $(realpath ../../../..)
OUTPUT_DIRECTORY := .
INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/cbor/spec $(EVERPARSE_HOME)/lib/everparse/cddl/spec $(EVERPARSE_HOME)/src/cddl/tool $(EVERPARSE_HOME)/lib/everparse/cbor/pulse $(EVERPARSE_HOME)/lib/everparse/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := *,-COSE,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool'

include $(EVERPARSE_HOME)/src/karamel.Makefile
include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile
