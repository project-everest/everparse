all: verify

EVERCBOR_SRC_PATH = $(realpath ../../../..)
INCLUDE_PATHS += $(realpath ..) $(realpath ../..) $(realpath ../../everparse) $(realpath ../../..) $(EVERCBOR_SRC_PATH)/lowparse $(EVERCBOR_SRC_PATH)/lowparse/pulse

FSTAR_DEP_OPTIONS := --extract '* -FStar.Tactics -FStar.Reflection -Pulse -PulseCore +Pulse.Class -Pulse.Lib +Pulse.Lib.Slice -LowParse.Pulse -CBOR +CBOR.Pulse.Raw.Test'

OUTPUT_DIRECTORY:=test-extract

include $(EVERCBOR_SRC_PATH)/pulse.Makefile
include $(EVERCBOR_SRC_PATH)/everparse.Makefile
include $(EVERCBOR_SRC_PATH)/common.Makefile

test-extract: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.Raw.Test=\*' -tmpdir $(OUTPUT_DIRECTORY) $^

.PHONY: test-extract
