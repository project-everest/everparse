all: extract

EVERPARSE_SRC_PATH = $(realpath ../../../..)

include $(EVERPARSE_SRC_PATH)/karamel.Makefile

RUST_DIRECTORY:=src

extract: $(RUST_DIRECTORY)/cbordet.rs

$(RUST_DIRECTORY)/cbordet.rs: ../krml/extracted/files.rsp
	$(KRML_HOME)/krml $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(RUST_DIRECTORY) -skip-compilation @$^

test: extract

.PHONY: all extract test
