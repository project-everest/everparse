all: extract

EVERPARSE_SRC_PATH = $(realpath ../../../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)

ifeq (,$(DICE_HOME))
  $(error "Please set DICE_HOME")
endif

OUTPUT_DIRECTORY := _output
INCLUDE_PATHS += \
$(EVERPARSE_SRC_PATH)/cddl/spec \
$(EVERPARSE_SRC_PATH)/cbor/spec \
$(EVERPARSE_SRC_PATH)/cbor/pulse \
$(EVERPARSE_SRC_PATH)/cddl/pulse \
$(EVERPARSE_SRC_PATH)/cddl/tool \
../util \
../_output \
$(DICE_HOME) \
$(DICE_HOME)/_cache

clean_rules += clean-output

# Whole-program extraction.  Every module a -bundle below names has to be a
# root: a bundle is packaging, not reachability.  [Prims] and Custard's own
# support modules join the [fstar] bundle, and the two abstract CBOR types are
# declared external because the -add-include'd CBORDetType.h defines them.
CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := CDDLTest.DPEMain
CUSTARD_ENTRY_MODULES += CBOR.Spec.Constants
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.C
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Dummy
CUSTARD_ROOTS := CDDLTest.DPEMain.fst
CUSTARD_EXTERN_TYPES := CBOR.Pulse.API.Det.Type.cbor_det_t
CUSTARD_EXTERN_TYPES += CBOR.Pulse.API.Det.Type.cbor_det_map_entry_t

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile

ALREADY_CACHED := *,-CDDLTest.DPE,-DPESlice,
FSTAR_OPTIONS += --warn_error -342

include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract: $(CUSTARD_KRML)
	$(KRML) -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*,Prims,Custard.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]'  -bundle CDDLTest.DPEMain=*[rename=CDDLExtractionTest] -add-include '"CBORDetType.h"' -no-prefix CBOR.Pulse.API.Det.Dummy -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -skip-compilation $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c
	for f in $(OUTPUT_DIRECTORY)/*.c; do $(CC) $(CFLAGS) -Wno-unused-function -I $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -c $$f -o $${f%.c}.o || exit 1; done

.PHONY: all extract

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
