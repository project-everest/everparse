all: extract

EVERPARSE_SRC_PATH = $(realpath ../../..)
SRC_DIRS += $(EVERPARSE_SRC_PATH)/cbor/pulse
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec

FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice,-CBOR.Spec,+CBOR.Spec.Constants'

ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY:=h-extracted
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

NONDET_C_DIRECTORY:=$(realpath ..)/nondet/c-extracted
DET_C_DIRECTORY:=$(realpath ../det/c)/extracted

clean_rules += clean-extracted

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

$(NONDET_C_DIRECTORY)/CBORNondetBase.h: $(filter-out %CBOR_Pulse_API_Det_Rust.krml %CBOR_Pulse_API_Det_C.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML_HOME)/krml $(KRML_OPTS) -faggressive-inlining -fnoshort-names -warn-error @1..27 -skip-linking -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Nondet.Type+CBOR.Pulse.API.Nondet.C=\*[rename=CBORNondetBase]' -no-prefix CBOR.Pulse.API.Nondet.C -no-prefix CBOR.Pulse.API.Nondet.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Nondet.Type -tmpdir $(NONDET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation $^
	test ! -e $(basename $@).c

$(DET_C_DIRECTORY)/CBORDetBase.h: $(filter-out %CBOR_Pulse_API_Det_Rust.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	$(KRML_HOME)/krml $(KRML_OPTS) -faggressive-inlining -warn-error @1..27 -skip-linking -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C+CBOR.Pulse.API.Det.C.Copy=\*[rename=CBORDetBase]' -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.API.Det.C.Copy -tmpdir $(DET_C_DIRECTORY) -header header.txt -skip-makefiles -skip-compilation $^
	test ! -e $(basename $@).c

extract: $(NONDET_C_DIRECTORY)/CBORNondetBase.h $(DET_C_DIRECTORY)/CBORDetBase.h

.PHONY: extract

clean-extracted:
	rm -rf extracted

.PHONY: clean-extracted
