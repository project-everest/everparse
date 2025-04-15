.PHONY: all
all: signtest verifytest test

EVERPARSE_SRC_PATH = $(realpath ../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
CACHE_DIRECTORY := $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_PATH)/lib/evercddl/lib $(EVERPARSE_PATH)/lib/evercddl/plugin $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(EVERPARSE_SRC_PATH)/cose/_output $(OUTPUT_DIRECTORY)

ALREADY_CACHED := Pulse,COSE.Format,CDDL,CBOR,
FSTAR_OPTIONS += --load_cmxs evercddl_lib --load_cmxs evercddl_plugin
FSTAR_OPTIONS += --warn_error -342 # noextract
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CDDL.Pulse.Bundle,-CDDL.Pulse.AST.Bundle,-CDDL.Tool'
FSTAR_FILES := CommonPulse.fst

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_HOME)/krml -fstar $(FSTAR_EXE) $(KRML_OPTS)

ALL_C_FILES := _output/CommonPulse.c

.PHONY: extract
extract: $(ALL_C_FILES)

_output/CommonPulse.c: $(ALL_KRML_FILES)
	$(KRML) -fnoshort-enums -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*[rename=fstar]' \
		-bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]' \
		-add-include '"CBORDetAbstract.h"' \
		-bundle 'COSE.Format=COSE.Format,C,CDDL.*' \
		-add-include '"COSE_Format.h"' \
		-bundle CommonPulse=*[rename=CommonPulse] \
		-no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CommonPulse \
		-skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -header noheader.txt

_output/COSE_Format.c: _output/CommonPulse.c

SANFLAGS = -fsanitize=address -fsanitize=undefined

CFLAGS += -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c

$(HACL_HOME)/dist/gcc-compatible/libevercrypt.a:
	$(MAKE) -C $(dir $@)

signtest: signtest.c common.c _output/CommonPulse.c _output/COSE_Format.c ../../cbor/pulse/det/c/CBORDet.c $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	$(CC) $(SANFLAGS) $(CFLAGS) $+ $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a -I _output -o $@

verifytest: verifytest.c common.c _output/CommonPulse.c _output/COSE_Format.c ../../cbor/pulse/det/c/CBORDet.c $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	$(CC) $(SANFLAGS) $(CFLAGS) $+ $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a -I _output -o $@

bench: bench.c common.c _output/CommonPulse.c _output/COSE_Format.c ../../cbor/pulse/det/c/CBORDet.c $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a
	clang -O3 $(CFLAGS) $+ $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a -I _output -o $@

.PHONY: test
test: signtest verifytest
	../interop/.venv/bin/python test.py