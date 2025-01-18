all: build

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec
ALREADY_CACHED := *,
FSTAR_DEP_OPTIONS := --extract CDDL.Spec.AST.Base,CDDL.Spec.AST.Elab,CDDL.Spec.AST.Driver,CBOR.Spec.Constants
OUTPUT_DIRECTORY := ocaml/evercddl-lib/extracted
FSTAR_DEP_FILE := ocaml.depend

include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(ALL_ML_FILES)

.PHONY: all extract

build: $(ALL_ML_FILES)

.PHONY: build
