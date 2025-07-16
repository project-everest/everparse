all: extract list

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/pulse $(EVERPARSE_SRC_PATH)/cbor/pulse 
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec/raw $(EVERPARSE_SRC_PATH)/cbor/spec/raw/everparse $(EVERPARSE_SRC_PATH)/cbor/pulse/raw $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/everparse $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

ALREADY_CACHED := *,
FSTAR_FILES := CDDL.Tool.Extraction.Rust.fst
OUTPUT_DIRECTORY := extraction-rust
FSTAR_DEP_FILE := extraction-rust.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool,+CDDL.Tool.Extraction.Rust'
FSTAR_OPTIONS += --warn_error -342 # noextract

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(ALL_KRML_FILES)

$(OUTPUT_DIRECTORY)/rust.lst: $(FSTAR_DEP_FILE)
	for f in $(notdir $(ALL_KRML_FILES)) ; do echo $$f ; done | sort > $@.tmp
	mv $@.tmp $@

list: $(OUTPUT_DIRECTORY)/rust.lst

.PHONY: all list extract
