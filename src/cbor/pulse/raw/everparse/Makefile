all: verify

EVERCBOR_SRC_PATH = $(realpath ../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(realpath ../../../spec) $(realpath ../../../spec/raw) $(realpath ../../../spec/raw/everparse) $(EVERCBOR_SRC_PATH)/lowparse $(EVERCBOR_SRC_PATH)/lowparse/pulse

FSTAR_DEP_OPTIONS := --extract '* -FStar.Tactics -FStar.Reflection -Pulse -PulseCore +Pulse.Class -Pulse.Lib +Pulse.Lib.Slice -LowParse.Pulse +LowParse.Pulse.Base -CBOR +CBOR.Spec.Raw.Base +CBOR.Pulse.Raw.EverParse.Test +CBOR.Spec.Raw.EverParse +CBOR.Spec.Constants +CBOR.Pulse.Raw.EverParse.Format +CBOR.Pulse.Raw.Format.Serialize +CBOR.Pulse.Raw.Type'

ALREADY_CACHED := *,-CBOR.Pulse.Raw.Format,-CBOR.Pulse.Raw.EverParse,
OUTPUT_DIRECTORY:=test-extract

include $(EVERCBOR_SRC_PATH)/pulse.Makefile
include $(EVERCBOR_SRC_PATH)/everparse.Makefile
include $(EVERCBOR_SRC_PATH)/common.Makefile

test-extr: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml $(KRML_OPTS) -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.Raw.EverParse.Test=\*' -tmpdir $(OUTPUT_DIRECTORY) $^

.PHONY: test-extr
