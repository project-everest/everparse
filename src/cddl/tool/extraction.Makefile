all: extract

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/pulse $(EVERPARSE_SRC_PATH)/cbor/pulse 
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec/raw $(EVERPARSE_SRC_PATH)/cbor/spec/raw/everparse $(EVERPARSE_SRC_PATH)/cbor/pulse/raw $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/everparse $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

ALREADY_CACHED := *,
FSTAR_FILES := $(wildcard CDDL.Tool.Extraction.*.fst)
OUTPUT_DIRECTORY := extraction
FSTAR_DEP_FILE := extraction.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool,+CDDL.Tool.Extraction'
FSTAR_OPTIONS += --warn_error -342 # noextract

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(ALL_KRML_FILES)

.PHONY: all extract
