all: build

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec
ALREADY_CACHED := *,
FSTAR_DEP_OPTIONS := --extract CDDL.Spec.AST.Base,CDDL.Spec.AST.Elab,CDDL.Spec.AST.Driver,CBOR.Spec.Constants
OUTPUT_DIRECTORY := ocaml/extracted
FSTAR_DEP_FILE := ocaml.depend

include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(ALL_ML_FILES)

.PHONY: all extract

EVERPARSE_CDDL=$(EVERPARSE_SRC_PATH)/../bin/cddl.exe
EVERPARSE_CDDL_MAIN=ocaml/_build/default/Main.exe

build: $(EVERPARSE_CDDL)

.PHONY: build

$(EVERPARSE_CDDL): $(EVERPARSE_CDDL_MAIN)
	mkdir -p $(dir $@)
	cp $< $@
	chmod +w $@ # because dune produces read-only executables

$(EVERPARSE_CDDL_MAIN): $(ALL_ML_FILES) $(filter-out %~,$(wildcard ocaml/*.ml*))
	cd ocaml && $(FSTAR_EXE) --ocamlenv dune build
