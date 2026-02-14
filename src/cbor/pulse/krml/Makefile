all: extract

EVERPARSE_SRC_PATH = $(realpath ../../..)
SRC_DIRS += $(EVERPARSE_SRC_PATH)/cbor/pulse
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/spec/raw $(EVERPARSE_SRC_PATH)/cbor/spec/raw/everparse $(EVERPARSE_SRC_PATH)/cbor/pulse/raw $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/everparse $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CBOR.Spec,+CBOR.Spec.Constants,+CBOR.Spec.Raw.EverParse,+CBOR.Spec.Raw.Base,+CBOR.Spec.Raw.Optimal'

ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY:=extracted
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
	$(KRML_HOME)/krml $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Type=CBOR.Pulse.Raw.Type,Pulse.Lib.Slice,CBOR.Pulse.Raw.Iterator.Base,CBOR.Pulse.Raw.Iterator,CBOR.Spec.Raw.Base[rename=CBORNondetType]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Nondet.C=\*[rename=CBORNondet]' -no-prefix CBOR.Pulse.API.Nondet.C -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(NONDET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

$(DET_C_DIRECTORY)/CBORDet.c: $(filter-out %CBOR_Pulse_API_Det_Rust.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML_HOME)/krml $(KRML_OPTS) -faggressive-inlining -warn-error @1..27 -skip-linking -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C+CBOR.Pulse.API.Det.C.Copy=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -no-prefix CBOR.Pulse.API.Det.C.Copy -no-prefix CBOR.Pulse.Raw.Copy -tmpdir $(DET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation -fextern-c -fparentheses $^

$(DET_RUST_DIRECTORY)/cbordetver.rs: $(filter-out %CBOR_Pulse_API_Det_C.krml,$(ALL_KRML_FILES))
	$(KRML_HOME)/krml $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Det.Rust=[rename=CBORDetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type=\*[rename=CBORDetVerAux]' -tmpdir $(DET_RUST_DIRECTORY) -skip-compilation $^

$(NONDET_RUST_DIRECTORY)/cbornondetver.rs: $(filter-out %CBOR_Pulse_API_Det_C.krml %CBOR_Pulse_API_Det_Rust.krml %CBOR_Pulse_API_Nondet_C.krml,$(ALL_KRML_FILES))
	$(KRML_HOME)/krml $(KRML_OPTS) -backend rust -fno-box -fkeep-tuples -fcontained-type cbor_raw_iterator -warn-error @1..27 -skip-linking -bundle 'CBOR.Pulse.API.Nondet.Rust=[rename=CBORNondetVer]' -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Nondet.Type=\*[rename=CBORNondetVerAux]' -tmpdir $(NONDET_RUST_DIRECTORY) -skip-compilation $^

extract-krml: $(ALL_KRML_FILES)

.PHONY: extract-krml

extract: extract-krml $(NONDET_C_DIRECTORY)/CBORNondet.c $(NONDET_RUST_DIRECTORY)/cbornondetver.rs $(DET_C_DIRECTORY)/CBORDet.c $(DET_RUST_DIRECTORY)/cbordetver.rs

.PHONY: extract

clean-extracted:
	rm -rf extracted

.PHONY: clean-extracted
