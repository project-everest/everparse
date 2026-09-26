all: extract

EVERPARSE_SRC_PATH = $(realpath ../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../../spec) $(realpath ../../spec/raw)
# ALREADY_CACHED := *,

FSTAR_FILES := CBOR.Pulse.API.Det.Type.fst
OUTPUT_DIRECTORY := extract-det-type
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

# Whole-program extraction. A karamel -bundle clause is packaging, not
# reachability, so each module named on the left of a `=' has to be rooted
# here by hand; CBOR.Spec.Constants is rooted because -no-prefix names it.
CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := CBOR.Pulse.API.Det.Type CBOR.Spec.Constants

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile
include $(EVERPARSE_SRC_PATH)/karamel.Makefile

.PHONY: extract

extract: $(CUSTARD_KRML)
	$(KRML_EXE) -bundle 'CBOR.Pulse.API.Det.Type=\*' -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $^
