all: test

EVERPARSE_SRC_PATH = $(realpath ../../..)
SRC_DIRS += $(realpath ..)
INCLUDE_PATHS += $(realpath ../../spec) $(realpath ../../spec/raw) $(realpath ../../spec/raw/everparse) $(realpath ../raw) $(realpath ../raw/everparse) $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice'

ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY:=extracted
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

$(OUTPUT_DIRECTORY)/CBORDet.c: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml $(KRML_OPTS) -warn-error @1..27 -skip-linking -bundle 'CBOR.Spec.Constants+CBOR.Pulse.Raw.Type+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det=\*[rename=CBORDet]' -no-prefix CBOR.Pulse.API.Det -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Spec.Constants -no-prefix CBOR.Pulse.API.Det.Type -no-prefix CBOR.Pulse.Raw.Type -tmpdir $(OUTPUT_DIRECTORY) -skip-compilation $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

extract: $(OUTPUT_DIRECTORY)/CBORDet.o

.PHONY: extract

test: extract
	+$(MAKE) -C $@

.PHONY: test
