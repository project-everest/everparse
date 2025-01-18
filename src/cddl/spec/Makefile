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

ocaml: $(ALL_CHECKED_FILES)
	+$(MAKE) -f $@.Makefile

.PHONY: ocaml

plugin: $(ALL_CHECKED_FILES)
	+$(MAKE) -f $@.Makefile

.PHONY: plugin

EVERPARSE_CDDL=$(EVERPARSE_SRC_PATH)/../bin/cddl.exe
EVERPARSE_CDDL_MAIN=ocaml/_build/default/Main.exe

build:
	cd ocaml && $(FSTAR_EXE) --ocamlenv dune build
	mkdir -p $(dir $(EVERPARSE_CDDL))
	cp $(EVERPARSE_CDDL_MAIN) $(EVERPARSE_CDDL)
	chmod +w $(EVERPARSE_CDDL) # because dune produces read-only executables

.PHONY: build

$(EVERPARSE_CDDL): $(EVERPARSE_CDDL_MAIN)

$(EVERPARSE_CDDL_MAIN): 


.PHONY: build
