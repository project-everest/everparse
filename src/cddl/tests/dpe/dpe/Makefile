all: extract

DICE_HOME := $(PULSE_HOME)/share/pulse/examples/dice

EVERPARSE_SRC_PATH = $(realpath ../../../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
INCLUDE_PATHS += \
$(EVERPARSE_SRC_PATH)/cddl/spec \
$(EVERPARSE_SRC_PATH)/cbor/spec \
$(EVERPARSE_SRC_PATH)/cbor/pulse \
$(EVERPARSE_SRC_PATH)/cddl/pulse \
$(EVERPARSE_SRC_PATH)/cddl/tool \
$(EVERPARSE_PATH)/lib/evercddl/lib \
$(EVERPARSE_PATH)/lib/evercddl/plugin \
../util \
../_output \
$(DICE_HOME) \
$(DICE_HOME)/_cache

clean_rules += clean-output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile

ALREADY_CACHED := *,-CDDLTest.DPE,-DPESlice,
FSTAR_OPTIONS += --load_cmxs evercddl_lib --load_cmxs evercddl_plugin
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool'

include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_HOME)/krml -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract: $(ALL_KRML_FILES)
	$(KRML) -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]'  -bundle CDDLTest.DPEMain=*[rename=CDDLExtractionTest] -add-include '"CBORDetAbstract.h"' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c

.PHONY: all extract

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
