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
FSTAR_FILES := $(OUTPUT_DIRECTORY)/COSE.Format.fst CommonPulse.fst

# Whole-program extraction.  Every module a -bundle below names has to be a
# root: a bundle is packaging, not reachability.  [Prims] and Custard's own
# support modules join the CBORDetVerAux bundle, which is the one the others
# depend on.
CUSTARD_BACKEND := KrmlRust
CUSTARD_ENTRY_MODULES := CommonPulse
CUSTARD_ENTRY_MODULES += COSE.Format
CUSTARD_ENTRY_MODULES += EverCrypt.Ed25519
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Rust
CUSTARD_ENTRY_MODULES += CBOR.Spec.Constants
CUSTARD_ENTRY_MODULES += CBOR.Pulse.Raw.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.Raw.Slice
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Type
CUSTARD_ROOTS := CommonPulse.fst

clean_rules += clean-output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

#KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract-krml: $(CUSTARD_KRML)

.PHONY: extract-krml

extract: $(CUSTARD_KRML)
	$(KRML) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking \
		-bundle 'CommonPulse=[rename=CommonPulse]' \
		-bundle 'EverCrypt.Ed25519=[rename=Ed25519]' \
		-bundle 'COSE.Format=[rename=COSEFormat]' \
		-bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' \
		-bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Det.Type=\*,Prims,Custard.\*[rename=CBORDetVerAux]' \
		-tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $(CUSTARD_KRML)

#	$(KRML) -bundle COSE.Format=*[rename=COSEFormat] -add-include '"CBORDetAbstract.h"' -no-prefix CBOR.Pulse.API.Det.Rust -no-prefix CBOR.Spec.Constants -skip-compilation $^ -tmpdir $(OUTPUT_DIRECTORY) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator

.PHONY: extract

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
