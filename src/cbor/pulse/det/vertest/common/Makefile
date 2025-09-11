all: verify test

EVERPARSE_SRC_PATH = $(realpath ../../../../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/pulse
ALREADY_CACHED := *,-CBORTest,
OUTPUT_DIRECTORY:=extracted
CBORDET_PATH := $(realpath ../../c)

CFLAGS += -I $(CBORDET_PATH)

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

.PHONY: extract test

extract: $(OUTPUT_DIRECTORY)/test.exe

$(OUTPUT_DIRECTORY)/test.exe: $(OUTPUT_DIRECTORY)/CBORTest.o
	$(CC) -o $@ $^ $(CBORDET_PATH)/CBORDet.o

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

$(OUTPUT_DIRECTORY)/CBORTest.c: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml $(KRML_OPTS) -warn-error @1..27 -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]' -bundle 'CBORTest.C=\*[rename=CBORTest]' -add-include '"CBORDetAbstract.h"' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBORTest.C -tmpdir $(OUTPUT_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation $^

$(OUTPUT_DIRECTORY)/CBORTest.rs: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -bundle 'FStar.\*,LowStar.\*,C.\*,PulseCore.\*,Pulse.\*[rename=fstar]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]' -bundle 'CBORTest.Rust=\*[rename=CBORTest]' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBORTest.C -tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $^

test: extract
	$(OUTPUT_DIRECTORY)/test.exe
