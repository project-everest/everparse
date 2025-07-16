all: extract

EVERPARSE_SRC_PATH = $(realpath ../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../../spec) $(realpath ../../spec/raw)
# ALREADY_CACHED := *,

FSTAR_FILES := CBOR.Pulse.API.Det.Type.fst
OUTPUT_DIRECTORY := extract-det-type
FSTAR_DEP_OPTIONS := --extract '*,-FStar,-Pulse,-PulseCore,-CBOR,+Pulse.Class,+Pulse.Lib.Slice,+CBOR.Spec.Constants,+CBOR.Pulse.API.Det.Type,+CBOR.Pulse.Raw.Type'
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

.PHONY: extract

extract: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml -bundle 'CBOR.Pulse.API.Det.Type=\*' -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $^
