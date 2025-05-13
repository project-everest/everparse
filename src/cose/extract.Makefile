EVERPARSE_SRC_PATH = $(realpath ..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_PATH)/lib/evercddl/lib $(EVERPARSE_PATH)/lib/evercddl/plugin $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := *,-COSE,
FSTAR_OPTIONS += --load_cmxs evercddl_lib --load_cmxs evercddl_plugin
FSTAR_OPTIONS += --warn_error -342 # noextract
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool'
FSTAR_FILES := $(OUTPUT_DIRECTORY)/COSE.Format.fst

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_HOME)/krml -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract: $(ALL_KRML_FILES)
	$(KRML) -fnoshort-enums -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]'  -bundle COSE.Format=*[rename=COSE_Format] -add-include '"CBORDetAbstract.h"' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -header noheader.txt

.PHONY: extract

C_FILES=COSE_Format.c COSE_Format.h CBORDetAPI.h

%.diff: extract
	diff c/$(basename $@) $(OUTPUT_DIRECTORY)/$(basename $@)

snapshot: extract
	mkdir -p c
	rm -f $(addprefix c/,$(C_FILES))
	cp $(addprefix $(OUTPUT_DIRECTORY)/,$(C_FILES)) c/

.PHONY: snapshot

test: $(addsuffix .diff,$(C_FILES))
