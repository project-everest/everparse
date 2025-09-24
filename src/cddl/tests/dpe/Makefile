all: dpe

EVERPARSE_SRC_PATH = $(realpath ../../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_PATH)/lib/evercddl/lib $(EVERPARSE_PATH)/lib/evercddl/plugin $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := *,-CDDLTest,
FSTAR_OPTIONS += --load_cmxs evercddl_lib --load_cmxs evercddl_plugin
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_FILES := $(OUTPUT_DIRECTORY)/CDDLTest.Test.fst

clean_rules += clean-test dpe.clean util.clean

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

$(OUTPUT_DIRECTORY)/CDDLTest.Test.fst: dpe.cddl dpe_postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $(OUTPUT_DIRECTORY) --fstar_only
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

# The Pulse DPE Makefile cannot be used outside of the Pulse
# repository, so we need to build it by hand
dice:
	+$(MAKE) -f dice.Makefile
#	+OTHERFLAGS='--admit_smt_queries true' $(MAKE) -C $(PULSE_HOME)/../share/pulse/examples/dice verify

.PHONY: dpe dice util
