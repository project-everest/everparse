EVERPARSE_SRC_PATH = $(realpath ../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/spec/raw $(EVERPARSE_SRC_PATH)/cbor/spec/raw/everparse $(EVERPARSE_SRC_PATH)/cbor/pulse/raw $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/slice-rust $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/everparse $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse
#INCLUDE_PATHS += ../verifiedinterop

CACHE_DIRECTORY := _output
ALREADY_CACHED := *,-COSE.Format,-CommonPulse,-CommonAbort,-EverCrypt,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Pervasives,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool'
FSTAR_FILES := $(OUTPUT_DIRECTORY)/COSE.Format.fst CommonPulse.fst

clean_rules += clean-output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

#KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

# Shared by the karamel-native and the Custard leg: the same five bundles
# define the crate's module structure either way.
COSE_RUST_BUNDLES := \
		-bundle 'CommonPulse=[rename=CommonPulse]' \
		-bundle 'EverCrypt.Ed25519=[rename=Ed25519]' \
		-bundle 'COSE.Format=[rename=COSEFormat]' \
		-bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' \
		-bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Det.Type=\*[rename=CBORDetVerAux]'

extract-krml: $(ALL_KRML_FILES)

.PHONY: extract-krml

extract: extract-krml
	$(KRML) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking \
		$(COSE_RUST_BUNDLES) \
		-tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $(ALL_KRML_FILES)

# Custard: replaces the F* --codegen krml step above with Custard's KrmlRust
# backend.  karamel then runs unchanged, on the same bundles.
CUSTARD_SLICE := rust
include $(EVERPARSE_SRC_PATH)/cose/custard.Makefile

CUSTARD_KRML_DIR := $(OUTPUT_DIRECTORY)/custard

extract-custard-krml: $(ALL_CHECKED_FILES)
	rm -rf $(CUSTARD_KRML_DIR)
	mkdir -p $(CUSTARD_KRML_DIR)
	$(CUSTARD_FSTAR) --custard_backend KrmlRust \
		$(addprefix --custard_entry_module ,$(CUSTARD_RUST_ENTRY_MODULES)) \
		--custard_split --odir $(CUSTARD_KRML_DIR) \
		$(OUTPUT_DIRECTORY)/COSE.Format.fst

# karamel exits 0 even when it fails to print a function, so the log is grepped
# rather than trusted.
extract-custard: extract-custard-krml
	$(KRML) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking \
		$(COSE_RUST_BUNDLES) \
		-tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $(CUSTARD_KRML_DIR)/*.krml \
		2>&1 | tee $(OUTPUT_DIRECTORY)/custard-krml.log
	@ ! grep -q 'ERROR printing' $(OUTPUT_DIRECTORY)/custard-krml.log || \
	  { echo 'karamel failed to print some functions:'; \
	    grep 'ERROR printing' $(OUTPUT_DIRECTORY)/custard-krml.log; exit 1; }

.PHONY: extract-custard extract-custard-krml

#	$(KRML) -bundle COSE.Format=*[rename=COSEFormat] -add-include '"CBORDetAbstract.h"' -no-prefix CBOR.Pulse.API.Det.Rust -no-prefix CBOR.Spec.Constants -skip-compilation $^ -tmpdir $(OUTPUT_DIRECTORY) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator

.PHONY: extract

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
