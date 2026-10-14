EVERPARSE_HOME = $(realpath ../../../../..)
OUTPUT_DIRECTORY := .
INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/cbor/spec $(EVERPARSE_HOME)/lib/everparse/cddl/spec $(EVERPARSE_HOME)/src/cddl/tool $(EVERPARSE_HOME)/lib/everparse/cbor/pulse $(EVERPARSE_HOME)/lib/everparse/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := *,-CDDLTest,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_FILES := $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst

# Whole-program extraction.  Every module a -bundle below names has to be a
# root: a bundle is packaging, not reachability.  [Prims] and Custard's own
# support modules join the [fstar] bundle, and the two abstract CBOR types are
# declared external because the -add-include'd CBORDetType.h defines them.
CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := CDDLTest.Test
CUSTARD_ENTRY_MODULES += CBOR.Spec.Constants
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.C
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Dummy
CUSTARD_ROOTS := $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst
CUSTARD_EXTERN_TYPES := CBOR.Pulse.API.Det.Type.cbor_det_t
CUSTARD_EXTERN_TYPES += CBOR.Pulse.API.Det.Type.cbor_det_map_entry_t

include $(EVERPARSE_HOME)/src/karamel.Makefile
include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract: $(CUSTARD_KRML)
	$(KRML) -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*,Prims,Custard.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]'  -bundle CDDLTest.Test=*[rename=CDDLExtractionTest] -add-include '"CBORDetType.h"' -no-prefix CBOR.Pulse.API.Det.Dummy -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_HOME)/include/everparse

.PHONY: extract
