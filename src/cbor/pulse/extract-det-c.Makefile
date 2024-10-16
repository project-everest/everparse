all: extract

EVERCBOR_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(realpath ../spec) $(realpath ../spec/raw) $(realpath ../spec/raw/everparse) raw raw/everparse $(EVERCBOR_SRC_PATH)/lowparse $(EVERCBOR_SRC_PATH)/lowparse/pulse

FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice'

ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY:=extract-det-c
# FSTAR_DEP_FILE := extract-det-c.depend
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

include $(EVERCBOR_SRC_PATH)/pulse.Makefile
include $(EVERCBOR_SRC_PATH)/everparse.Makefile
include $(EVERCBOR_SRC_PATH)/common.Makefile

extract: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml $(KRML_OPTS) -warn-error @1..27 -skip-linking -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(OUTPUT_DIRECTORY) $^

.PHONY: extract
