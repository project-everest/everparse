all: extract-all

EVERPARSE_SRC_PATH = $(realpath ../../..)
EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output

$(OUTPUT_DIRECTORY)/rfc9711/CDDLTest_Test.c: rfc9711.cddl cwt.cddl $(EVERPARSE_SRC_PATH)/cose/cose.cddl $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl
	mkdir -p $(dir $@)
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $(dir $@) --tmpdir $(dir $@)

extract-all: $(OUTPUT_DIRECTORY)/rfc9711/CDDLTest_Test.c

.PHONY: extract-all all
