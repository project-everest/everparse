all: extract

EVERPARSE_SRC_PATH = $(realpath ../../..)
SRC_DIRS += $(EVERPARSE_SRC_PATH)/cbor/pulse
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/spec/raw $(EVERPARSE_SRC_PATH)/cbor/spec/raw/everparse $(EVERPARSE_SRC_PATH)/cbor/pulse/raw $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/everparse $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

# Selects the byte_slice backend implementation of CBOR.Pulse.Raw.Slice (c or rust).
# byte_slice0 is an abstract seam (CBOR.Pulse.Raw.Slice.fsti); each backend's .fst
# unfolds it differently at extraction time, so the slice-typed byte fields of
# CBOR.Pulse.Raw.Type extract differently per backend. The C extraction must use
# slice-c (its plain `byte_slice = slice uint8_t` abbrev survives KaRaMeL
# monomorphization and names the emitted C struct `byte_slice`, avoiding the
# duplicate-typedef collision in CDDL/COSE consumer headers); the Rust extraction
# must use slice-rust (byte_slice0 unfolds straight to slice uint8_t, keeping the
# native &[u8] model type). Exactly one impl must be on the include path, so the two
# backends are extracted in separate passes (see the `extract` target) into separate
# output directories.
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/slice-$(CBOR_SLICE_BACKEND)

FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CBOR.Spec,+CBOR.Spec.Constants,+CBOR.Spec.Raw.EverParse,+CBOR.Spec.Raw.Base,+CBOR.Spec.Raw.Optimal'

# The slice backend impl (CBOR.Pulse.Raw.Slice in slice-$(CBOR_SLICE_BACKEND)) is
# selected per pass by include path and is not part of the committed checked-file
# cache. Its .fst.checked is built by the backend's own Makefile (see the explicit
# delegation rule near the bottom of this file and
# src/cbor/pulse/raw/slice-$(CBOR_SLICE_BACKEND)/Makefile), so here we treat it as
# already cached and only consume it: that keeps the slice out of ALL_CHECKED_FILES
# (so it is not also built by common.Makefile's `$(ALL_CHECKED_FILES): %.checked`
# rule) while leaving it as a prerequisite of the slice .krml. The normal extraction
# entry point overrides ALREADY_CACHED (src/cbor/Makefile passes
# '*,-CBOR,CBOR.Pulse.Raw.Slice,', which likewise re-caches the slice while keeping
# the rest of CBOR uncached); this default applies when krml is built directly.
ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY:=extracted-$(CBOR_SLICE_BACKEND)
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

clean_rules += clean-extracted

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

# CBOR.Pulse.Raw.Slice's backend .fst is verified by its own directory's Makefile
# (it is treated as already cached here, ALREADY_CACHED above), so delegate building
# its .fst.checked there rather than re-deriving it in this pass. krml extraction of
# the slice module (bundled into the CBORxxxType header) then consumes this .checked.
# The recipe fires only when the .checked is missing or older than its source; on the
# normal path cbor-verify has already built it via the same Makefile, so this is a
# no-op safety net for direct/standalone krml builds.
CBOR_SLICE_DIR := $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/slice-$(CBOR_SLICE_BACKEND)
$(CBOR_SLICE_DIR)/CBOR.Pulse.Raw.Slice.fst.checked: $(CBOR_SLICE_DIR)/CBOR.Pulse.Raw.Slice.fst
	+$(MAKE) -C $(CBOR_SLICE_DIR)

extract-krml: $(ALL_KRML_FILES)

.PHONY: extract-krml
