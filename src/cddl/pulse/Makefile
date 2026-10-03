all: verify

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(realpath ../spec) $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/pulse

ALREADY_CACHED := *,-CDDL.Pulse,
FSTAR_OPTIONS += --warn_error -342
OUTPUT_DIRECTORY := _output

# Whole-program extraction. A karamel -bundle clause is packaging, not
# reachability: CDDL.Pulse.Test, named on the left of the `=', has to be
# rooted here by hand.
CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := CDDL.Pulse.Test
CUSTARD_ROOTS := CDDL.Pulse.Test.fst

clean_rules += clean-output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE)

extract: $(CUSTARD_KRML)
#	$(KRML) -bundle CBOR.Spec.Constants+CBOR.Pulse.Type+CBOR.Pulse.Extern=[rename=CBOR] -no-prefix CBOR.Spec.Constants,CBOR.Pulse.Type,CBOR.Pulse.Extern -bundle CDDL.Pulse.Test=*[rename=CDDLExtractionTest] -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY)
	$(KRML) -bundle CDDL.Pulse.Test=*[rename=CDDLExtractionTest] -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY)

.PHONY: extract

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
