EVERPARSE_SRC_PATH = $(realpath ../../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/spec/raw $(EVERPARSE_SRC_PATH)/cbor/spec/raw/everparse $(EVERPARSE_SRC_PATH)/cbor/pulse/raw $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/slice-rust $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/everparse $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

ALREADY_CACHED := *,-CDDLTest,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Pervasives,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool'
FSTAR_FILES := $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst

clean_rules += clean-test

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

#KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract: $(ALL_KRML_FILES)
	$(KRML) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CDDLTest.Test=[rename=CDDLExtractionTest]' -bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type=\*[rename=CBORDetVerAux]' -tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $^

#	$(KRML) -bundle CDDLTest.Test=*[rename=CDDLExtractionTest] -add-include '"CBORDetAbstract.h"' -no-prefix CBOR.Pulse.API.Det.Rust -no-prefix CBOR.Spec.Constants -skip-compilation $^ -tmpdir $(OUTPUT_DIRECTORY) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator

.PHONY: extract

# ---------------------------------------------------------------- Custard ---
#
# The Rust leg is Custard --custard_backend KrmlRust followed by karamel,
# unchanged and on the same bundles: Custard replaces F* --codegen krml, not
# karamel.  Entry modules are the union of the `+` lists of the -bundle flags
# above -- the same program stated the other way round.
CUSTARD_SLICE := rust
CUSTARD_C_ENTRY_MODULES =
include $(EVERPARSE_SRC_PATH)/cddl/tests/custard.Makefile

CUSTARD_RUST_ENTRY_MODULES = CDDLTest.Test $(CUSTARD_CBOR_RUST_ENTRY_MODULES)

CUSTARD_KRML_DIR := $(OUTPUT_DIRECTORY)/custard

extract-custard-krml: $(ALL_CHECKED_FILES)
	rm -rf $(CUSTARD_KRML_DIR)
	mkdir -p $(CUSTARD_KRML_DIR)
	$(CUSTARD_FSTAR) --custard_backend KrmlRust \
		$(addprefix --custard_entry_module ,$(CUSTARD_RUST_ENTRY_MODULES)) \
		--custard_split --odir $(CUSTARD_KRML_DIR) \
		$(OUTPUT_DIRECTORY)/CDDLTest.Test.fst

# karamel exits 0 even when it fails to print a function, so the log is
# grepped rather than trusted.  (Same guard as src/cose/generate-rust.)
extract-custard: extract-custard-krml
	$(KRML) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CDDLTest.Test=[rename=CDDLExtractionTest]' -bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type=\*[rename=CBORDetVerAux]' -tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $(CUSTARD_KRML_DIR)/*.krml \
		2>&1 | tee $(OUTPUT_DIRECTORY)/custard-krml.log
	@ ! grep -q 'ERROR printing' $(OUTPUT_DIRECTORY)/custard-krml.log || \
	  { echo 'karamel failed to print some functions:'; \
	    grep 'ERROR printing' $(OUTPUT_DIRECTORY)/custard-krml.log; exit 1; }

.PHONY: extract-custard extract-custard-krml

clean-test:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-test
