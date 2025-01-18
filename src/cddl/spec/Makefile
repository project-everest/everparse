all: verify

EVERPARSE_SRC_PATH = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec

ALREADY_CACHED := *,-CDDL.Spec,
# FSTAR_OPTIONS += --warn_error -342
# FSTAR_DEP_OPTIONS := --extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse -PulseCore +Pulse.Class -Pulse.Lib'
# OUTPUT_DIRECTORY := _output

include $(EVERPARSE_SRC_PATH)/common.Makefile

# KRML=$(KRML_HOME)/krml $(KRML_OPTS)

# extract: $(ALL_KRML_FILES)
# 	$(KRML) -bundle C -bundle CBOR.Spec.Constants+CBOR.Pulse.Type+CBOR.Pulse.Extern=[rename=CBOR] -no-prefix CBOR.Spec.Constants,CBOR.Pulse.Type,CBOR.Pulse.Extern -bundle CDDLExtractionTest.Assume+CDDLExtractionTest.Bytes+CDDLExtractionTest.BytesUnwrapped+CDDLExtractionTest.Choice=*[rename=CDDLExtractionTest] -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY)

# .PHONY: extract

ocaml.done: $(ALL_CHECKED_FILES)
	rm -f $@
	+$(MAKE) -f $(basename $@).Makefile
	touch $@

plugin.done: $(ALL_CHECKED_FILES)
	rm -f $@
	+$(MAKE) -f $(basename $@).Makefile
	touch $@

EVERPARSE_CDDL=$(EVERPARSE_SRC_PATH)/../bin/cddl.exe

build: $(EVERPARSE_CDDL)

.PHONY: build

$(EVERPARSE_CDDL): ocaml.done plugin.done $(wildcard ocaml/*/*.ml*)
	cd ocaml && $(FSTAR_EXE) --ocamlenv dune build
	cd ocaml && dune install --prefix=$(realpath $(EVERPARSE_SRC_PATH)/..)

.PHONY: build
