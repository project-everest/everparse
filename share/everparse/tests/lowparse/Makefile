all: verify extract-all

EVERPARSE_SRC_PATH ?= $(realpath ../../../../src)
LOWPARSE_PULSE_HOME ?= $(EVERPARSE_SRC_PATH)/lowparse/pulse

INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse $(LOWPARSE_PULSE_HOME)
ALREADY_CACHED := *,-LowParseTestLib,-LowParseExample,
OTHERFLAGS += --warn_error +272

OUTPUT_DIRECTORY := _output
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,-PulseCore,+Pulse.Class,+Pulse.Lib.Slice'

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

ifeq ($(OS),Darwin)
KRML_OPTS += -ccopt -Wno-tautological-constant-out-of-range-compare
endif

KRML=$(KRML_HOME)/krml -fstar $(FSTAR_EXE) $(KRML_OPTS)

EXAMPLES=Example3 ExampleConstInt32le Example2 Example5 Example7 Example8 Example9 Example10 Example11 Example12 ExampleDepLen

extract-all: $(EXAMPLES)

$(EXAMPLES): %: verify %/a.out

%/a.out: $(ALL_KRML_FILES)
	$(KRML) -bundle 'LowParse$*=*[rename=LowParse$*]' -no-prefix 'LowParse$*' \
		-warn-error '@2' -tmpdir $* $^ -o $@
	./$@

clean:
	rm -rf $(OUTPUT_DIRECTORY) $(addsuffix /, $(EXAMPLES)) .depend

.PHONY: all extract-all clean $(EXAMPLES)
