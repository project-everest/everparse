all: extract

.PHONY: all

EVERPARSE_SRC_PATH = $(realpath ../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
CACHE_DIRECTORY := $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_PATH)/lib/evercddl/lib $(EVERPARSE_PATH)/lib/evercddl/plugin $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)
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
FSTAR_OPTIONS += --load_cmxs evercddl_lib --load_cmxs evercddl_plugin
FSTAR_OPTIONS += --warn_error -342 # noextract
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool'
FSTAR_FILES := $(OUTPUT) $(wildcard *.fst *.fsti)

clean_rules += clean-output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_HOME)/krml -fstar $(FSTAR_EXE) $(KRML_OPTS)

# internal/COSE_Format.h is unavoidable because Pulse.Lib.Slice.len is used in both COSE.Format and COSE.EverCrypt
BASE_C_FILES=COSE_EverCrypt.c COSE_EverCrypt.h COSE_Format.c COSE_Format.h CBORDetAPI.h
INTERNAL_C_FILES=COSE_Format.h
C_FILES=$(BASE_C_FILES) $(addprefix internal/,$(INTERNAL_C_FILES))

.PHONY: extract-krml
extract-krml: $(ALL_KRML_FILES)

# Include paths matching krml's built-in cc invocation, used by the post-extract syntax check.
COSE_CC_INCLUDES = -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal \
	-I $(OUTPUT_DIRECTORY) -I $(OUTPUT_DIRECTORY)/internal -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c

.PHONY: extract
extract: extract-krml
	$(KRML) -faggressive-inlining -fnoshort-enums -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*[rename=fstar]' \
		-bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C+CBOR.Pulse.API.Det.Dummy=CBOR.\*[rename=CBORDetAPI]' \
		-bundle 'COSE.EverCrypt=Abort,EverCrypt.Ed25519' \
		-bundle 'COSE.Format=*' \
		-no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Dummy -no-prefix Abort \
		-add-include '"CBORDetType.h"' \
		-skip-compilation $(ALL_KRML_FILES) -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -header noheader.txt
# The CBOR Det types are now concrete (CBORDetType.h, no CAbstractStruct). krml therefore
# re-emits the shared monomorphic instance Pulse_Lib_Slice_slice__uint8_t inside COSE_Format.h,
# colliding with the identical definition that COSE_Format.h already #includes from CBORDetType.h.
# Drop COSE's duplicate; the included CBORDetType.h provides the canonical definition.
	perl -0pi -e 's/typedef struct Pulse_Lib_Slice_slice__uint8_t_s\n\{\n  uint8_t \*elt;\n  size_t len;\n\}\nPulse_Lib_Slice_slice__uint8_t;\n//' $(OUTPUT_DIRECTORY)/COSE_Format.h
	$(CC) -fsyntax-only -Wall -Werror $(COSE_CC_INCLUDES) $(OUTPUT_DIRECTORY)/COSE_Format.c $(OUTPUT_DIRECTORY)/COSE_EverCrypt.c

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
ifeq ($(EVERPARSE_NO_DIFF),) # Set this variable to disable diffs
test: $(addsuffix .diff,$(C_FILES))
endif

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
