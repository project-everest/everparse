CBOR_SLICE_BACKEND := rust
include extract.Makefile

parent_dir := $(realpath ..)
ifeq ($(OS),Windows_NT)
  parent_dir := $(shell cygpath -m $(parent_dir))
endif
DET_RUST_DIRECTORY:=$(parent_dir)/det/rust-extracted
NONDET_RUST_DIRECTORY:=$(parent_dir)/nondet/rust-extracted

$(DET_RUST_DIRECTORY)/cbordetver.rs: $(filter-out %CBOR_Pulse_API_Det_C.krml,$(ALL_KRML_FILES))
	$(KRML_EXE) $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.Dummy=\*[rename=CBORDetVerAux]' -tmpdir $(DET_RUST_DIRECTORY) -skip-compilation $^

$(NONDET_RUST_DIRECTORY)/cbornondetver.rs: $(filter-out %CBOR_Pulse_API_Det_C.krml %CBOR_Pulse_API_Det_Rust.krml %CBOR_Pulse_API_Nondet_C.krml,$(ALL_KRML_FILES))
	$(KRML_EXE) $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Rust=[rename=CBORNondetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Nondet.Type=\*[rename=CBORNondetVerAux]' -tmpdir $(NONDET_RUST_DIRECTORY) -skip-compilation $^

extract: $(DET_RUST_DIRECTORY)/cbordetver.rs $(NONDET_RUST_DIRECTORY)/cbornondetver.rs

.PHONY: extract

include $(EVERPARSE_SRC_PATH)/cbor/custard.Makefile

# Custard's KrmlRust backend, then karamel exactly as above: the -bundle and
# -no-prefix flags select on karamel modules, and --custard_split gives the
# single .krml one karamel module per F* module for them to match against.
#
# karamel exits 0 even when it fails to print a function, so the log is grepped
# rather than trusted.
$(DET_RUST_DIRECTORY)/custard/cbordetver.rs: $(ALL_CHECKED_FILES)
	rm -rf $(dir $@) $(DET_RUST_DIRECTORY)/custard-krml
	mkdir -p $(dir $@) $(DET_RUST_DIRECTORY)/custard-krml
	$(CUSTARD_FSTAR) --custard_backend KrmlRust \
		$(addprefix --custard_entry_module ,$(CUSTARD_DET_RUST_ENTRY)) \
		--custard_split --odir $(DET_RUST_DIRECTORY)/custard-krml $(CUSTARD_DET_RUST_ROOT)
	$(KRML_EXE) $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.Dummy=\*[rename=CBORDetVerAux]' -tmpdir $(dir $@) -skip-compilation $(DET_RUST_DIRECTORY)/custard-krml/*.krml 2>&1 | tee $(DET_RUST_DIRECTORY)/custard-krml/krml.log
	@ ! grep -q 'ERROR printing' $(DET_RUST_DIRECTORY)/custard-krml/krml.log || \
	  { echo 'karamel failed to print some functions:'; grep 'ERROR printing' $(DET_RUST_DIRECTORY)/custard-krml/krml.log; exit 1; }

$(NONDET_RUST_DIRECTORY)/custard/cbornondetver.rs: $(ALL_CHECKED_FILES)
	rm -rf $(dir $@) $(NONDET_RUST_DIRECTORY)/custard-krml
	mkdir -p $(dir $@) $(NONDET_RUST_DIRECTORY)/custard-krml
	$(CUSTARD_FSTAR) --custard_backend KrmlRust \
		$(addprefix --custard_entry_module ,$(CUSTARD_NONDET_RUST_ENTRY)) \
		--custard_split --odir $(NONDET_RUST_DIRECTORY)/custard-krml $(CUSTARD_NONDET_RUST_ROOT)
	$(KRML_EXE) $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Rust=[rename=CBORNondetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.Raw.Slice+CBOR.Pulse.API.Nondet.Type=\*[rename=CBORNondetVerAux]' -tmpdir $(dir $@) -skip-compilation $(NONDET_RUST_DIRECTORY)/custard-krml/*.krml 2>&1 | tee $(NONDET_RUST_DIRECTORY)/custard-krml/krml.log
	@ ! grep -q 'ERROR printing' $(NONDET_RUST_DIRECTORY)/custard-krml/krml.log || \
	  { echo 'karamel failed to print some functions:'; grep 'ERROR printing' $(NONDET_RUST_DIRECTORY)/custard-krml/krml.log; exit 1; }

extract-custard: $(DET_RUST_DIRECTORY)/custard/cbordetver.rs $(NONDET_RUST_DIRECTORY)/custard/cbornondetver.rs

.PHONY: extract-custard
