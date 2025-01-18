all: build

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec
ALREADY_CACHED := *,
FSTAR_DEP_OPTIONS := --extract CDDL.Spec.AST.Plugin.Base,CDDL.Spec.AST.Plugin
OUTPUT_DIRECTORY := ocaml/evercddl-plugin/extracted
FSTAR_DEP_FILE := plugin.depend
FSTAR_ML_CODEGEN := Plugin

include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(ALL_ML_FILES)

.PHONY: all extract

build: $(ALL_ML_FILES)
