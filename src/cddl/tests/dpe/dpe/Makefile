.DEFAULT_GOAL := all

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

include $(EVERPARSE_SRC_PATH)/custard-detect.Makefile
include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile

ALREADY_CACHED := *,-CDDLTest.DPE,-DPESlice,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Pervasives,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool'

include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract: $(ALL_KRML_FILES)
	$(KRML) -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]'  -bundle CDDLTest.DPEMain=*[rename=CDDLExtractionTest] -add-include '"CBORDetType.h"' -no-prefix CBOR.Pulse.API.Det.Dummy -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -skip-compilation $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c
	for f in $(OUTPUT_DIRECTORY)/*.c; do $(CC) $(CFLAGS) -Wno-unused-function -I $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -c $$f -o $${f%.c}.o || exit 1; done

.PHONY: all extract

# ---------------------------------------------------------------- Custard ---
#
# Custard emits the whole program as one translation unit, so there is no
# CBORDetAPI.h to include and no separate CBOR object: the det CBOR API is
# folded in.  The entry-module list is the union of the `+' lists of the
# -bundle flags above; the `fstar' bundle is purely a karamel-side grouping of
# the F*/Pulse runtime and has no Custard counterpart, because Custard emits
# whatever the entry points reach and nothing else.
#
# Like the karamel leg, this is a compile-only test: it checks that the
# generated C is accepted by the C compiler, and does not link or run.
CUSTARD_EVERPARSE_SRC := $(EVERPARSE_SRC_PATH)
CUSTARD_C_ENTRY_MODULES = CDDLTest.DPEMain $(CUSTARD_CBOR_DET_ENTRY_MODULES)

include $(EVERPARSE_SRC_PATH)/cddl/tests/custard.Makefile

CUSTARD_C_DIR := $(OUTPUT_DIRECTORY)/custard

extract-custard: $(ALL_CHECKED_FILES)
	rm -rf $(CUSTARD_C_DIR)
	mkdir -p $(CUSTARD_C_DIR)
	$(CUSTARD_FSTAR) $(CUSTARD_C_FLAGS) \
	  $(addprefix --include ,$(DICE_HOME) $(DICE_HOME)/_cache ../util ../_output) \
	  CDDLTest.DPEMain.fst -o $(CURDIR)/$(CUSTARD_C_DIR)/CDDLExtractionTest.c
	$(call custard-cbor-shim,$(CUSTARD_C_DIR),CDDLExtractionTest.h)
	$(CC) $(CFLAGS) -Wno-unused-function -I $(CUSTARD_C_DIR) \
	  -c $(CUSTARD_C_DIR)/CDDLExtractionTest.c -o $(CUSTARD_C_DIR)/CDDLExtractionTest.o

.PHONY: extract-custard

# Dispatch: under CUSTARD=1 the default build uses Custard's direct-to-C
# backend instead of F* --codegen krml + karamel.  This has to sit after the
# include of custard-detect.Makefile above: a rule's prerequisites are expanded
# where the rule is written, so stating it at the top of the file would read
# CUSTARD before it had been set.  extract-custard and extract are both always
# available by name, whichever way CUSTARD is set.
all: $(if $(filter 1,$(CUSTARD)),extract-custard,extract)

.PHONY: all

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
