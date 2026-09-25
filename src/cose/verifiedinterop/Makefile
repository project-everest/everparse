all: extract

.PHONY: all

EVERPARSE_SRC_PATH = $(realpath ../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
CACHE_DIRECTORY := $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)
OUTPUT:=$(OUTPUT_DIRECTORY)/COSE.Format.fst

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

$(OUTPUT): ../cose-sign.cddl $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname COSE.Format --odir $(dir $(OUTPUT)) --fstar_only $(CDDL_ADMIT)
	cp extract0.Makefile $(OUTPUT_DIRECTORY)/Makefile

ALREADY_CACHED := *,-COSE,-Abort,-EverCrypt
FSTAR_OPTIONS += --warn_error -342 # noextract
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_FILES := $(OUTPUT) $(wildcard *.fst *.fsti)

# Whole-program extraction.  Every module a -bundle below names has to be a
# root: a bundle is packaging, not reachability.  [Prims] and Custard's own
# support modules join the [fstar] bundle, and the two abstract CBOR types are
# declared external because the -add-include'd CBORDetType.h defines them.
CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := COSE.EverCrypt
CUSTARD_ENTRY_MODULES += COSE.Format
CUSTARD_ENTRY_MODULES += Abort
CUSTARD_ENTRY_MODULES += EverCrypt.Ed25519
CUSTARD_ENTRY_MODULES += CBOR.Spec.Constants
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.C
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Dummy
CUSTARD_ROOTS := COSE.EverCrypt.fst
CUSTARD_EXTERN_TYPES := CBOR.Pulse.API.Det.Type.cbor_det_t
CUSTARD_EXTERN_TYPES += CBOR.Pulse.API.Det.Type.cbor_det_map_entry_t

clean_rules += clean-output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

# internal/COSE_Format.h is unavoidable because Pulse.Lib.Slice.len is used in both COSE.Format and COSE.EverCrypt
# internal/fstar.h carries the externs (EverCrypt, the CBOR serializer helpers)
# that the [fstar] bundle collects.
BASE_C_FILES=COSE_EverCrypt.c COSE_EverCrypt.h COSE_Format.c COSE_Format.h CBORDetAPI.h
INTERNAL_C_FILES=COSE_Format.h fstar.h
C_FILES=$(BASE_C_FILES) $(addprefix internal/,$(INTERNAL_C_FILES))

.PHONY: extract-krml
extract-krml: $(CUSTARD_KRML)

.PHONY: extract
extract: $(CUSTARD_KRML)
	$(KRML) -faggressive-inlining -fnoshort-enums -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*,Prims,Custard.\*[rename=fstar]' \
		-skip-makefiles \
		-bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C+CBOR.Pulse.API.Det.Dummy=CBOR.\*[rename=CBORDetAPI]' \
		-add-include '"CBORDetType.h"' -no-prefix CBOR.Pulse.API.Det.Dummy \
		-bundle 'COSE.EverCrypt=Abort,EverCrypt.Ed25519' \
		-bundle 'COSE.Format=*' \
		-no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix Abort \
		-skip-linking $(CUSTARD_KRML) -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -header noheader.txt

%.diff: extract
	diff ../c/$(basename $@) $(OUTPUT_DIRECTORY)/$(basename $@)

.PHONY: %.diff

snapshot: extract
	mkdir -p ../c/internal
	rm -f $(addprefix ../c/,$(C_FILES))
	cp $(addprefix $(OUTPUT_DIRECTORY)/,$(BASE_C_FILES)) ../c/
	cp $(addprefix $(OUTPUT_DIRECTORY)/internal/,$(INTERNAL_C_FILES)) ../c/internal/

.PHONY: snapshot

test: extract
ifeq ($(EVERPARSE_CHECK_DIFF),1) # Set this variable to enable diffs
test: $(addsuffix .diff,$(C_FILES))
endif

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
