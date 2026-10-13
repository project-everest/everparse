all: extract

EVERPARSE_HOME = $(realpath ../..)
INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/lowparse
ALREADY_CACHED := *,-ArithParse,

OUTPUT_DIRECTORY := _output
clean_rules += clean-output
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := ArithParse.Impl
CUSTARD_ROOTS := ArithParse.Impl.fst

include $(EVERPARSE_HOME)/src/karamel.Makefile
include $(EVERPARSE_HOME)/src/everparse.Makefile
include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

extract: $(CUSTARD_KRML)
	$(KRML) -bundle 'ArithParse.Impl=*,Prims,Custard.\*[rename=ArithParse]' -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY) -I $(EVERPARSE_HOME)/src/cbor/pulse/det/c

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: extract clean-output
