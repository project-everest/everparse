all: dpe

EVERPARSE_HOME := $(realpath ../../../..)
include $(EVERPARSE_HOME)/src/windows.Makefile

OUTPUT_DIRECTORY := _output
INCLUDE_PATHS += $(EVERPARSE_HOME)/lib/everparse/cbor/spec $(EVERPARSE_HOME)/src/cddl/spec $(EVERPARSE_HOME)/src/cddl/tool $(EVERPARSE_HOME)/lib/everparse/cbor/pulse $(EVERPARSE_HOME)/src/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := *,-CDDLTest,
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_FILES := $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst

clean_rules += clean-test dpe.clean util.clean

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

include $(EVERPARSE_HOME)/src/karamel.Makefile
include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile

$(OUTPUT_DIRECTORY)/CDDLTest.Test.fst: dpe.cddl dpe_postlude.cddl
	$(EVERPARSE_HOME)/bin/cddl.exe $^ --odir $(OUTPUT_DIRECTORY) --fstar_only $(CDDL_ADMIT)
	cp extract0.Makefile $(OUTPUT_DIRECTORY)/Makefile

clean-test:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-test

dpe: $(ALL_CHECKED_FILES) dice util
	+$(MAKE) -C $@

util:
	+$(MAKE) -C $@

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean

include dice_home.Makefile

# The Pulse DPE Makefile cannot be used outside of the Pulse
# repository, so we need to build it by hand
dice: $(NEED_DICE)
	+$(MAKE) -f dice.Makefile

.PHONY: dpe dice util
