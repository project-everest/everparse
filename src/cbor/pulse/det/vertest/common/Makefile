all: verify test

EVERPARSE_SRC_PATH = $(realpath ../../../../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/pulse
ALREADY_CACHED := *,-CBORTest,
OUTPUT_DIRECTORY:=extracted
CBORDET_PATH := $(realpath ../../c)

CFLAGS += -I $(CBORDET_PATH)

# Whole-program extraction.  The [CBORDetAPI] bundle is header-only here -- its
# definitions come from the prebuilt CBORDet.o this test links against -- but
# karamel still has to be handed the program that fills it, so every module the
# bundle names is rooted.  [Prims] and Custard's own support modules join the
# [fstar] bundle, or the CBOR types they carry would land in the test file and
# make the two bundles mutually dependent.  The two abstract CBOR types come
# from the -add-include'd CBORDetType.h; declaring them external stops Custard
# emitting its own incomplete typedef for each.
CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := CBORTest.C
CUSTARD_ENTRY_MODULES += CBOR.Spec.Constants
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.C
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Dummy
CUSTARD_ROOTS := CBORTest.C.fst
CUSTARD_EXTERN_TYPES := CBOR.Pulse.API.Det.Type.cbor_det_t
CUSTARD_EXTERN_TYPES += CBOR.Pulse.API.Det.Type.cbor_det_map_entry_t

clean_rules += clean-extracted

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

.PHONY: extract test

extract: $(OUTPUT_DIRECTORY)/test.exe

$(OUTPUT_DIRECTORY)/test.exe: $(OUTPUT_DIRECTORY)/CBORTest.o
	$(CC) -o $@ $^ $(CBORDET_PATH)/CBORDet.o

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

$(OUTPUT_DIRECTORY)/CBORTest.c: $(CUSTARD_KRML)
	$(KRML_EXE) $(KRML_OPTS) -warn-error @1..27 -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*,Prims,Custard.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C+CBOR.Pulse.API.Det.Dummy=CBOR.\*[rename=CBORDetAPI]' -bundle 'CBORTest.C=\*[rename=CBORTest]' -add-include '"CBORDetType.h"' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Dummy -no-prefix CBORTest.C -tmpdir $(OUTPUT_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation $^

test: extract
	$(OUTPUT_DIRECTORY)/test.exe

clean-extracted:
	rm -rf extracted

.PHONY: clean-extracted
