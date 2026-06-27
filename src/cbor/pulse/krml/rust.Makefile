CBOR_SLICE_BACKEND := rust
include extract.Makefile

DET_RUST_DIRECTORY:=$(realpath ../det)/rust-extracted
NONDET_RUST_DIRECTORY:=$(realpath ..)/nondet/rust-extracted

$(DET_RUST_DIRECTORY)/cbordetver.rs: $(filter-out %CBOR_Pulse_API_Det_C.krml,$(ALL_KRML_FILES))
	$(KRML_EXE) $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.Dummy=\*[rename=CBORDetVerAux]' -tmpdir $(DET_RUST_DIRECTORY) -skip-compilation $^

$(NONDET_RUST_DIRECTORY)/cbornondetver.rs: $(filter-out %CBOR_Pulse_API_Det_C.krml %CBOR_Pulse_API_Det_Rust.krml %CBOR_Pulse_API_Nondet_C.krml,$(ALL_KRML_FILES))
	$(KRML_EXE) $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Rust=[rename=CBORNondetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Nondet.Type=\*[rename=CBORNondetVerAux]' -tmpdir $(NONDET_RUST_DIRECTORY) -skip-compilation $^

extract: $(DET_RUST_DIRECTORY)/cbordetver.rs $(NONDET_RUST_DIRECTORY)/cbornondetver.rs

.PHONY: extract
