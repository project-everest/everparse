all: verify extract

EVERCBOR_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(realpath ..)

include $(EVERCBOR_SRC_PATH)/pulse.Makefile
include $(EVERCBOR_SRC_PATH)/karamel.Makefile

ALREADY_CACHED := *,-CBOR.Pulse,
# FSTAR_DEP_OPTIONS := --extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse -PulseCore +Pulse.Class +Pulse.Lib -Pulse.Lib.Core -Pulse.Lib.Pervasives -Pulse.Lib.Forall -Pulse.Lib.Primitives -Pulse.Lib.HigherArray'
FSTAR_DEP_OPTIONS := --extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse -PulseCore +Pulse.Class -Pulse.Lib'
OUTPUT_DIRECTORY := _output

include $(EVERCBOR_SRC_PATH)/common.Makefile

extract: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml -warn-error @1..27 -bundle C -bundle CBOR.Spec.Constants+CBOR.Pulse.Type+CBOR.Pulse.Extern=[rename=CBOR] -no-prefix CBOR.Spec.Constants,CBOR.Pulse.Type,CBOR.Pulse.Extern -bundle CBOR.Pulse=* -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY)

.PHONY: extract
