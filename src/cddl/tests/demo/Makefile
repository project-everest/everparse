all: extract-all

EVERPARSE_SRC_PATH = $(realpath ../../..)

OUTPUT=_output/CDDLTest.Test.fst

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

$(OUTPUT): test.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $(dir $(OUTPUT)) --fstar_only $(CDDL_ADMIT)

extract-all: $(OUTPUT) $(wildcard *.fst)
	+$(MAKE) -f extract.Makefile test

.PHONY: extract-all all

clean_rules += clean-output

clean-output:
	rm -rf _output

.PHONY: clean-output

# Uncomment if you want to edit the produced F* file
include extract.Makefile
