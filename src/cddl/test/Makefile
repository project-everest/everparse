all: extract-all

EVERPARSE_SRC_PATH = $(realpath ../..)

OUTPUT_DIRECTORY=_output
OUTPUT=$(OUTPUT_DIRECTORY)/CDDLTest.Test.fst

$(OUTPUT): dpe.cddl dpe_postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $(dir $(OUTPUT)) --fstar_only
	cp extract0.Makefile $(OUTPUT_DIRECTORY)/Makefile

extract-all: $(OUTPUT)
	+$(MAKE) -f extract.Makefile extract

.PHONY: extract-all all

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
