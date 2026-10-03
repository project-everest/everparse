CBOR_SLICE_BACKEND := rust
CBOR_API ?= det

# The roots of this pass: every module named on the left of a karamel -bundle
# clause below, plus the bundle names themselves (see extract.Makefile).
CUSTARD_ENTRY_MODULES := CBOR.Spec.Constants
CUSTARD_ENTRY_MODULES += CBOR.Pulse.Raw.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.Raw.Slice
ifeq (det,$(CBOR_API))
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Rust
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Type
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Det.Dummy
CUSTARD_ROOTS := $(realpath ../raw/CBOR.Pulse.API.Det.Rust.fst)
else
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Nondet.Rust
CUSTARD_ENTRY_MODULES += CBOR.Pulse.API.Nondet.Type
CUSTARD_ROOTS := $(realpath ../raw/CBOR.Pulse.API.Nondet.Rust.fst)
endif

include extract.Makefile

parent_dir := $(realpath ..)
ifeq ($(OS),Windows_NT)
  parent_dir := $(shell cygpath -m $(parent_dir))
endif
DET_RUST_DIRECTORY:=$(parent_dir)/det/rust-extracted
NONDET_RUST_DIRECTORY:=$(parent_dir)/nondet/rust-extracted

ifeq (det,$(CBOR_API))

$(DET_RUST_DIRECTORY)/cbordetver.rs: $(CUSTARD_KRML)
	$(KRML_EXE) $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.Dummy=\*[rename=CBORDetVerAux]' -tmpdir $(DET_RUST_DIRECTORY) -skip-compilation $^

extract: $(DET_RUST_DIRECTORY)/cbordetver.rs

else

$(NONDET_RUST_DIRECTORY)/cbornondetver.rs: $(CUSTARD_KRML)
	$(KRML_EXE) $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Rust=[rename=CBORNondetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Nondet.Type=\*[rename=CBORNondetVerAux]' -tmpdir $(NONDET_RUST_DIRECTORY) -skip-compilation $^

extract: $(NONDET_RUST_DIRECTORY)/cbornondetver.rs

endif

.PHONY: extract
