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
	$(KRML) -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]'  -bundle CDDLTest.DPEMain=*[rename=CDDLExtractionTest] -add-include '"CBORDetType.h"' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Dummy -skip-compilation $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c
# The CBOR Det types are now concrete (CBORDetType.h). krml re-emits the shared
# monomorphic instance Pulse_Lib_Slice_slice__uint8_t inside CDDLExtractionTest.h,
# colliding with the identical definition included from CBORDetType.h. Drop the
# duplicate; the included CBORDetType.h provides the canonical definition.
	perl -0pi -e 's/typedef struct Pulse_Lib_Slice_slice__uint8_t_s\n\{\n  uint8_t \*elt;\n  size_t len;\n\}\nPulse_Lib_Slice_slice__uint8_t;\n//' $(OUTPUT_DIRECTORY)/CDDLExtractionTest.h
	for f in $(OUTPUT_DIRECTORY)/*.c; do $(CC) $(CFLAGS) -Wno-unused-function -I $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -c $$f -o $${f%.c}.o || exit 1; done

.PHONY: all extract

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
