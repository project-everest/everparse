all: extract-all

EVERPARSE_SRC_PATH = $(realpath ../..)

OUTPUT=_output/CDDLTest.Test.fst

$(OUTPUT): test.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $(dir $(OUTPUT))

extract-all: $(OUTPUT)
	+$(MAKE) -f extract.Makefile extract

.PHONY: extract-all all

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
