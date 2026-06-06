all: extract

EVERPARSE_SRC_PATH = $(realpath ../../..)
SRC_DIRS += $(EVERPARSE_SRC_PATH)/cbor/pulse
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/spec/raw $(EVERPARSE_SRC_PATH)/cbor/spec/raw/everparse $(EVERPARSE_SRC_PATH)/cbor/pulse/raw $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/everparse $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

# Selects the byte_slice backend implementation of CBOR.Pulse.Raw.Slice (c or rust).
# byte_slice0 is an abstract seam (CBOR.Pulse.Raw.Slice.fsti); each backend's .fst
# unfolds it differently at extraction time, so the slice-typed fields of
# CBOR.Pulse.Raw.EverParse.Type extract differently per backend. The C extraction
# must use slice-c (its plain `byte_slice = slice uint8_t` abbrev survives KaRaMeL
# monomorphization and names the emitted C struct `byte_slice`, avoiding the
# duplicate-typedef collision in CDDL/COSE consumer headers); the Rust extraction
# must use slice-rust (byte_slice0 unfolds straight to slice uint8_t, keeping the
# native &[u8] model type). Exactly one impl must be on the include path, so the two
# backends are extracted in separate passes (see the `extract` target) into separate
# output directories.
CBOR_SLICE_BACKEND ?= c
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/slice-$(CBOR_SLICE_BACKEND)

FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CBOR.Spec,+CBOR.Spec.Constants,+CBOR.Spec.Raw.EverParse,+CBOR.Spec.Raw.Base,+CBOR.Spec.Raw.Optimal'

ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY:=extracted-$(CBOR_SLICE_BACKEND)
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

NONDET_C_DIRECTORY:=$(realpath ..)/nondet/c-extracted
DET_C_DIRECTORY:=$(realpath ../det/c)/extracted
DET_RUST_DIRECTORY:=$(realpath ../det)/rust-extracted
NONDET_RUST_DIRECTORY:=$(realpath ..)/nondet/rust-extracted

clean_rules += clean-extracted

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

$(NONDET_C_DIRECTORY)/CBORNondet.c: $(filter-out %CBOR_Pulse_API_Det_Rust.krml %CBOR_Pulse_API_Det_C.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML_HOME)/krml $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Type=CBOR.Pulse.Raw.EverParse.Type,CBOR.Pulse.Raw.Slice,Pulse.Lib.Slice,LowParse.PulseParse.Iterator.Type,CBOR.Spec.Raw.Base[rename=CBORNondetType]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Nondet.C=\*[rename=CBORNondet]' -no-prefix CBOR.Pulse.API.Nondet.C -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Pulse.Raw.EverParse.Type -no-prefix CBOR.Pulse.Raw.Slice -tmpdir $(NONDET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

$(DET_C_DIRECTORY)/CBORDet.c: $(filter-out %CBOR_Pulse_API_Det_Rust.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML_HOME)/krml $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Type=CBOR.Pulse.Raw.EverParse.Type,CBOR.Pulse.Raw.Slice,Pulse.Lib.Slice,LowParse.PulseParse.Iterator.Type,CBOR.Spec.Raw.Base[rename=CBORDetType]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.C+CBOR.Pulse.API.Det.C.Copy+CBOR.Pulse.API.Det.Dummy=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.EverParse.Type -no-prefix CBOR.Pulse.Raw.Slice -no-prefix CBOR.Pulse.API.Det.C.Copy -no-prefix CBOR.Pulse.Raw.Copy -no-prefix CBOR.Pulse.API.Det.Dummy -tmpdir $(DET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

$(DET_RUST_DIRECTORY)/cbordetver.rs: $(filter-out %CBOR_Pulse_API_Det_C.krml,$(ALL_KRML_FILES))
# NOTE: this Rust target must be built with CBOR_SLICE_BACKEND=rust (see the `extract`
# target and CBOR.Pulse.Raw.Slice). That selects the slice-rust implementation of
# byte_slice0, so CBOR.Pulse.Raw.EverParse.Type's slice-typed fields extract to the
# native &[u8] model type with no `byte_slice` abbrev to poison monomorphization. The
# C targets are built with CBOR_SLICE_BACKEND=c, which homes the `byte_slice` struct
# name. The two backends therefore consume disjoint per-pass .krml directories.
	$(KRML_HOME)/krml $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -fcontained-type iterator__ -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.EverParse.Type+CBOR.Pulse.API.Det.Type=\*[rename=CBORDetVerAux]' -tmpdir $(DET_RUST_DIRECTORY) -skip-compilation $^

$(NONDET_RUST_DIRECTORY)/cbornondetver.rs: $(filter-out %CBOR_Pulse_API_Det_C.krml %CBOR_Pulse_API_Det_Rust.krml,$(ALL_KRML_FILES))
	$(KRML_HOME)/krml $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -fcontained-type iterator__ -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Rust=[rename=CBORNondetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.EverParse.Type+CBOR.Pulse.API.Nondet.Type=\*[rename=CBORNondetVerAux]' -tmpdir $(NONDET_RUST_DIRECTORY) -skip-compilation $^

# The slice-typed fields of CBOR.Pulse.Raw.EverParse.Type extract differently per
# backend (see CBOR.Pulse.Raw.Slice), so C and Rust are extracted in two passes, each
# selecting the matching slice-* implementation via CBOR_SLICE_BACKEND and writing to
# its own extracted-$(CBOR_SLICE_BACKEND) directory.
extract-krml:
	+$(MAKE) CBOR_SLICE_BACKEND=c extract-krml-backend
	+$(MAKE) CBOR_SLICE_BACKEND=rust extract-krml-backend

extract-krml-backend: $(ALL_KRML_FILES)

.PHONY: extract-krml extract-krml-backend

extract:
	+$(MAKE) CBOR_SLICE_BACKEND=c extract-c-backend
	+$(MAKE) CBOR_SLICE_BACKEND=rust extract-rust-backend

extract-c-backend: $(NONDET_C_DIRECTORY)/CBORNondet.c $(DET_C_DIRECTORY)/CBORDet.c

extract-rust-backend: $(DET_RUST_DIRECTORY)/cbordetver.rs $(NONDET_RUST_DIRECTORY)/cbornondetver.rs

.PHONY: extract extract-c-backend extract-rust-backend

clean-extracted:
	rm -rf extracted extracted-c extracted-rust

.PHONY: clean-extracted
