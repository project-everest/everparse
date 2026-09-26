all: verify extract-all

EVERPARSE_SRC_PATH ?= $(realpath ../../../../src)
LOWPARSE_PULSE_HOME ?= $(EVERPARSE_SRC_PATH)/lowparse/pulse

INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse $(LOWPARSE_PULSE_HOME)
ALREADY_CACHED := *,-LowParseTestLib,-LowParseExample,
OTHERFLAGS += --warn_error +272

OUTPUT_DIRECTORY := _output
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

EXAMPLES=Example3 ExampleConstInt32le Example5 Example7 Example8 Example9 Example10 Example11 Example12

# One whole-program extraction covering every example, then one karamel run per
# example to package it.  A bundle is packaging, not reachability, so each
# example module has to be its own root.
CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := $(addprefix LowParse,$(EXAMPLES))
CUSTARD_ROOTS := LowParseExample3.fst

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

ifeq ($(OS),Darwin)
KRML_OPTS += -ccopt -Wno-tautological-constant-out-of-range-compare
endif

ifeq ($(OS),Windows_NT)
  local_curdir := $(shell cygpath -m $(CURDIR))
else
  local_curdir := $(CURDIR)
endif
KRML_OPTS += -skip-compilation

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract-all: $(EXAMPLES)

$(EXAMPLES): %: verify %/a.out

%/a.out: $(CUSTARD_KRML)
	$(KRML) -bundle 'LowParse$*=*,Prims,Custard.\*[rename=LowParse$*]' -no-prefix 'LowParse$*' \
		-warn-error '@2' -tmpdir $* $^ -o $@
	$(CC) -I $(local_curdir) -o $@ $*/LowParse$*.c
	./$@

clean:
	rm -rf $(OUTPUT_DIRECTORY) $(addsuffix /, $(EXAMPLES)) .depend

.PHONY: all extract-all clean $(EXAMPLES)
