all: verify extract

EVERCBOR_SRC_PATH = $(realpath ..)
INCLUDE_PATHS += $(EVERCBOR_SRC_PATH)/cbor $(EVERCBOR_SRC_PATH)/cbor/pulse

include $(EVERCBOR_SRC_PATH)/pulse.Makefile
include $(EVERCBOR_SRC_PATH)/karamel.Makefile

ALREADY_CACHED := *,-CDDL,-CDDLExtractionTest,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse -PulseCore +Pulse.Class -Pulse.Lib'
OUTPUT_DIRECTORY := _output

include $(EVERCBOR_SRC_PATH)/common.Makefile

KRML=$(KRML_HOME)/krml $(KRML_OPTS)

extract: $(ALL_KRML_FILES)
	$(KRML) -bundle C -bundle CBOR.Spec.Constants+CBOR.Pulse.Type+CBOR.Pulse.Extern=[rename=CBOR] -no-prefix CBOR.Spec.Constants,CBOR.Pulse.Type,CBOR.Pulse.Extern -bundle CDDLExtractionTest.Assume+CDDLExtractionTest.Bytes+CDDLExtractionTest.BytesUnwrapped+CDDLExtractionTest.Choice=*[rename=CDDLExtractionTest] -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY)

.PHONY: extract
