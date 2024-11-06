all: extract

EVERPARSE_SRC_PATH = $(realpath ../../../..)
SRC_DIRS += $(EVERPARSE_SRC_PATH)/cbor/pulse
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/spec/raw $(EVERPARSE_SRC_PATH)/cbor/spec/raw/everparse $(EVERPARSE_SRC_PATH)/cbor/pulse/raw $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/everparse $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice'

ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY:=extracted
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

C_DIRECTORY:=$(realpath ../c)
RUST_DIRECTORY:=$(realpath ../rust/src)

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

$(C_DIRECTORY)/CBORDet.c: $(ALL_KRML_FILES)
	mkdir -p $(dir $@)
	$(KRML_HOME)/krml $(KRML_OPTS) -warn-error @1..27 -skip-linking -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation $^

$(RUST_DIRECTORY)/cbordet.rs: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(RUST_DIRECTORY) -skip-compilation $^

extract: $(C_DIRECTORY)/CBORDet.c $(RUST_DIRECTORY)/cbordet.rs

.PHONY: extract
