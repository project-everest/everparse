all: extract

EVERPARSE_SRC_PATH = $(realpath ../../../..)
SRC_DIRS += $(EVERPARSE_SRC_PATH)/cbor/pulse
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cbor/spec/raw $(EVERPARSE_SRC_PATH)/cbor/spec/raw/everparse $(EVERPARSE_SRC_PATH)/cbor/pulse/raw $(EVERPARSE_SRC_PATH)/cbor/pulse/raw/everparse $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice'

ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY:=extracted
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

$(OUTPUT_DIRECTORY)/files.rsp: $(ALL_KRML_FILES)
	for f in $^ ; do echo $(CURDIR)/$$f ; done > $@.tmp
	mv $@.tmp $@

extract: $(OUTPUT_DIRECTORY)/files.rsp

.PHONY: extract
