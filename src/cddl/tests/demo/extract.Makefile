EVERPARSE_SRC_PATH = $(realpath ../../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
SRC_PATHS += $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := *,-CDDLTest,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Pervasives,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool'
FSTAR_FILES := $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst CDDLTest.Client.fst

clean_rules += clean-test

include $(EVERPARSE_SRC_PATH)/custard-detect.Makefile
include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

$(OUTPUT_DIRECTORY)/CDDLExtractionTest.o: $(ALL_KRML_FILES)
	$(KRML) -fnoshort-enums -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]'  -bundle CDDLTest.Client+CDDLTest.Test=*[rename=CDDLExtractionTest] -add-include '"CBORDetType.h"' -no-prefix CBOR.Pulse.API.Det.Dummy -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants  -skip-compilation $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c
	$(CC) $(CFLAGS) -I $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -c $(OUTPUT_DIRECTORY)/CDDLExtractionTest.c -o $@

$(OUTPUT_DIRECTORY)/test.exe: $(OUTPUT_DIRECTORY)/CDDLExtractionTest.o client.c
	$(CC) $(CFLAGS) -Wall -o $@ $^ $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.o -I $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c

# ---------------------------------------------------------------- Custard ---
#
# Custard emits the whole program as one translation unit, so there is no
# CBORDetAPI.h and no CBORDet.o to link: the det CBOR API is folded in.  The
# entry-module list is the union of the `+` lists of the karamel -bundle flags
# above, which is the same program stated the other way round.

CUSTARD_C_ENTRY_MODULES = \
  CDDLTest.Client CDDLTest.Test $(CUSTARD_CBOR_DET_ENTRY_MODULES)

include $(EVERPARSE_SRC_PATH)/cddl/tests/custard.Makefile

CUSTARD_C_DIR := $(OUTPUT_DIRECTORY)/custard

$(CUSTARD_C_DIR)/CDDLExtractionTest.c: $(ALL_CHECKED_FILES)
	rm -rf $(CUSTARD_C_DIR)
	mkdir -p $(CUSTARD_C_DIR)
	$(CUSTARD_FSTAR) $(CUSTARD_C_FLAGS) \
	  $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst \
	  -o $(CURDIR)/$@
	$(call custard-cbor-shim,$(CUSTARD_C_DIR),CDDLExtractionTest.h)

$(CUSTARD_C_DIR)/test.exe: $(CUSTARD_C_DIR)/CDDLExtractionTest.c client.c
	$(CC) $(CFLAGS) -Wall -DEVERPARSE_CUSTARD -o $@ $^ -I $(CUSTARD_C_DIR)

extract-custard: $(CUSTARD_C_DIR)/test.exe

.PHONY: extract-custard

ifeq (1,$(CUSTARD))
extract: $(CUSTARD_C_DIR)/test.exe

test: extract
	$(CUSTARD_C_DIR)/test.exe
else
extract: $(OUTPUT_DIRECTORY)/test.exe

test: extract
	$(OUTPUT_DIRECTORY)/test.exe
endif

.PHONY: extract test

clean-test:
	rm -f $(OUTPUT_DIRECTORY)/CDDLExtractionTest.o $(OUTPUT_DIRECTORY)/test.exe
	rm -rf $(CUSTARD_C_DIR)

.PHONY: clean-test
