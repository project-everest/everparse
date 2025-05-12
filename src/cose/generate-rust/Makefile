all: build-rust

EVERPARSE_SRC_PATH = $(realpath ../..)

OUTPUT=_output/COSE.Format.fst

$(OUTPUT): ../cose.cddl ../../cddl/spec/postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname COSE.Format --odir $(dir $(OUTPUT)) --rust

extract-all: $(OUTPUT)
	+$(MAKE) -f extract.Makefile extract

SNAPSHOT_FILES=cbordetveraux cbordetver commonpulse coseformat

snapshot: extract-all
	for f in $(SNAPSHOT_FILES) ; do cp _output/$$f.rs ../rust/src/ ; done

.PHONY: extract-all snapshot all

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
