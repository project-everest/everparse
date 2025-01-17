all: verify

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(realpath ../spec) $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/pulse

ALREADY_CACHED := *,-CDDL.Pulse,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice'
OUTPUT_DIRECTORY := _output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML=$(KRML_HOME)/krml -fstar $(FSTAR_EXE)

extract: $(ALL_KRML_FILES)
#	$(KRML) -bundle CBOR.Spec.Constants+CBOR.Pulse.Type+CBOR.Pulse.Extern=[rename=CBOR] -no-prefix CBOR.Spec.Constants,CBOR.Pulse.Type,CBOR.Pulse.Extern -bundle CDDL.Pulse.Test=*[rename=CDDLExtractionTest] -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY)
	$(KRML) -bundle CDDL.Pulse.Test=*[rename=CDDLExtractionTest] -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY)

.PHONY: extract
