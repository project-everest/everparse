all: extract

EVERPARSE_SRC_PATH := $(realpath ../../../../src)
include $(EVERPARSE_SRC_PATH)/windows.Makefile

SRC_DIRS += $(realpath ..)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse $(EVERPARSE_SRC_PATH)/lowparse/pulse

FSTAR_OPTIONS += --warn_error -342

# EverParse3d.Interpreter is specialized away in generated code (the `specialize`
# tactic), exactly as in the Low* prelude, so it is never extracted itself.
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Pervasives,+Pulse.Lib.Slice,+Pulse.Lib.ArrayPtr,-EverParse3d.Interpreter,-EverParse3d.Smoke'

ALREADY_CACHED := '*,'
OUTPUT_DIRECTORY := extracted
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

clean_rules += clean-extracted

include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

extract-krml: $(ALL_KRML_FILES)

.PHONY: extract-krml

# common.Makefile's clean-krml only removes $(OUTPUT_DIRECTORY)/*.krml, which
# leaves the directory and the .depend it holds behind. Drop the lot.
clean-extracted:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-extracted
