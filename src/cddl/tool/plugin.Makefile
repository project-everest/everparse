all: build

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec
FSTAR_FILES := CDDL.Tool.Plugin.Base.fst CDDL.Tool.Plugin.fst
ALREADY_CACHED := *,
FSTAR_DEP_OPTIONS := --extract CDDL.Tool.Plugin.Base,CDDL.Tool.Plugin
OUTPUT_DIRECTORY := ocaml/evercddl-plugin/extracted
FSTAR_DEP_FILE := plugin.depend
FSTAR_ML_CODEGEN := Plugin

include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(ALL_ML_FILES)

.PHONY: all extract

build: $(ALL_ML_FILES)
