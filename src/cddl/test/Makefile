all: verify

EVERPARSE_SRC_PATH = $(realpath ../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_PATH)/lib/evercddl/lib $(EVERPARSE_PATH)/lib/evercddl/plugin $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse

ALREADY_CACHED := *,-CDDLTest,
FSTAR_OPTIONS += --load_cmxs evercddl_lib --load_cmxs evercddl_plugin
# FSTAR_DEP_OPTIONS := --extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse -PulseCore +Pulse.Class -Pulse.Lib'
# OUTPUT_DIRECTORY := _output

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
