all: build

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/pulse
FSTAR_FILES := $(EVERPARSE_SRC_PATH)/cddl/spec/CDDL.Spec.AST.Base.fst $(EVERPARSE_SRC_PATH)/cddl/spec/CDDL.Spec.AST.Elab.fst $(EVERPARSE_SRC_PATH)/cddl/spec/CDDL.Spec.AST.Driver.fst CDDL.Tool.Gen.fst $(EVERPARSE_SRC_PATH)/cbor/spec/CBOR.Spec.Constants.fst
ALREADY_CACHED := *,
FSTAR_DEP_OPTIONS := --extract CDDL.Spec.AST.Base,CDDL.Spec.AST.Elab,CDDL.Spec.AST.Driver,CDDL.Tool.Gen,CBOR.Spec.Constants,CDDL.Pulse.AST.Ancillaries
OUTPUT_DIRECTORY := ocaml/evercddl-lib/extracted
FSTAR_DEP_FILE := ocaml.depend
FSTAR_ML_CODEGEN := Plugin

include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(ALL_ML_FILES)

.PHONY: all extract

build: $(ALL_ML_FILES)

.PHONY: build
