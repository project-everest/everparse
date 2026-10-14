EVERPARSE_HOME = $(realpath ../../../../..)
OUTPUT_DIRECTORY := _output
INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/cbor/spec $(EVERPARSE_HOME)/lib/everparse/cddl/spec $(EVERPARSE_HOME)/src/cddl/tool $(EVERPARSE_HOME)/lib/everparse/cbor/pulse $(EVERPARSE_HOME)/lib/everparse/cddl/pulse $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/cbor/spec $(EVERPARSE_HOME)/lib/everparse/cbor/spec/raw $(EVERPARSE_HOME)/lib/everparse/cbor/spec/raw/everparse $(EVERPARSE_HOME)/lib/everparse/cbor/pulse/raw $(EVERPARSE_HOME)/lib/everparse/cbor/pulse/raw/slice-rust $(EVERPARSE_HOME)/lib/everparse/cbor/pulse/raw/everparse $(EVERPARSE_HOME)/lib/everparse/lowparse

ALREADY_CACHED := *,-CDDLTest,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_FILES := $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst

clean_rules += clean-test

# Whole-program extraction.  Every module a -bundle below names has to be a
# root: a bundle is packaging, not reachability.
CUSTARD_BACKEND := KrmlRust
CUSTARD_ENTRY_MODULES := CDDLTest.Test
CUSTARD_ENTRY_MODULES += CBOR.Spec.Constants
CUSTARD_ENTRY_MODULES += CBOR.Pulse.Raw.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.Raw.Slice
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Rust
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Dummy
CUSTARD_ROOTS := $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst

include $(EVERPARSE_HOME)/src/karamel.Makefile
include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile

#KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract: $(CUSTARD_KRML)
	$(KRML) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CDDLTest.Test=[rename=CDDLExtractionTest]' -bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type=\*[rename=CBORDetVerAux]' -tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $^

#	$(KRML) -bundle CDDLTest.Test=*[rename=CDDLExtractionTest] -add-include '"CBORDetAbstract.h"' -no-prefix CBOR.Pulse.API.Det.Rust -no-prefix CBOR.Spec.Constants -skip-compilation $^ -tmpdir $(OUTPUT_DIRECTORY) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator

.PHONY: extract

clean-test:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-test
