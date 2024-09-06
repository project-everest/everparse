all: verify

EVERCBOR_SRC_PATH = $(realpath ../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(realpath ../../everparse) $(realpath ../../..) $(EVERCBOR_SRC_PATH)/lowparse $(EVERCBOR_SRC_PATH)/lowparse/pulse

FSTAR_DEP_OPTIONS := --extract '* -FStar.Tactics -FStar.Reflection -Pulse -PulseCore +Pulse.Class -Pulse.Lib +Pulse.Lib.Slice -LowParse.Pulse -CBOR +CBOR.Spec.Raw.Base +CBOR.Pulse.Raw.Test +CBOR.Spec.Raw.Format +CBOR.Spec.Constants +CBOR.Pulse.Raw.Format'

ALREADY_CACHED := *,-CBOR.Pulse.Raw.Format,-CBOR.Pulse.Raw.Match.Serialized,-CBOR.Pulse.Raw.Parse,-CBOR.Pulse.Raw.Serialized,-CBOR.Pulse.Raw.Test,
OUTPUT_DIRECTORY:=test-extract

include $(EVERCBOR_SRC_PATH)/pulse.Makefile
include $(EVERCBOR_SRC_PATH)/everparse.Makefile
include $(EVERCBOR_SRC_PATH)/common.Makefile

test-extract: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml $(KRML_OPTS) -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.Raw.Test=\*' -tmpdir $(OUTPUT_DIRECTORY) $^

.PHONY: test-extract
