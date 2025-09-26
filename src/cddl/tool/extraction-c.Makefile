all: extract list

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/pulse $(EVERPARSE_SRC_PATH)/cbor/pulse

ALREADY_CACHED := *,
FSTAR_FILES := CDDL.Tool.Extraction.C.fst
OUTPUT_DIRECTORY := extraction-c
FSTAR_DEP_FILE := extraction-c.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool,+CDDL.Tool.Extraction.C'
FSTAR_OPTIONS += --warn_error -342 # noextract

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(ALL_KRML_FILES)

list: $(OUTPUT_DIRECTORY)/c.lst

$(OUTPUT_DIRECTORY)/c.lst: $(FSTAR_DEP_FILE)
	for f in $(notdir $(ALL_KRML_FILES)) ; do echo $$f ; done | sort > $@.tmp
	mv $@.tmp $@

.PHONY: all list extract
