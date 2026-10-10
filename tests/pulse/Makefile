all: extract

EVERPARSE_SRC_PATH = $(realpath ../../src)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/lowparse/pulse
ALREADY_CACHED := *,-ArithParse,

OUTPUT_DIRECTORY := _output
clean_rules += clean-output
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := ArithParse.Impl
CUSTARD_ROOTS := ArithParse.Impl.fst

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/everparse.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract: $(CUSTARD_KRML)
	$(KRML) -bundle 'ArithParse.Impl=*,Prims,Custard.\*[rename=ArithParse]' -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: extract clean-output
