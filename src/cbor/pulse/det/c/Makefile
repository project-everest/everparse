all: extract

EVERPARSE_SRC_PATH = $(realpath ../../../..)
OUTPUT_DIRECTORY:=extracted

include $(EVERPARSE_SRC_PATH)/karamel.Makefile

extract: $(OUTPUT_DIRECTORY)/CBORDet.o

.PHONY: extract

$(OUTPUT_DIRECTORY)/CBORDet.c: ../krml/extracted/files.rsp
	mkdir -p $(dir $@)
	$(KRML_HOME)/krml $(KRML_OPTS) -warn-error @1..27 -skip-linking -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(OUTPUT_DIRECTORY) -skip-compilation @$^

test: extract
	+$(MAKE) -C $@

.PHONY: all test

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<
