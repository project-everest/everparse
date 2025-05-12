all: build-rust

EVERPARSE_SRC_PATH = $(realpath ../..)

OUTPUT=_output/COSE.Format.fst

$(OUTPUT): ../cose.cddl ../../cddl/spec/postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname COSE.Format --odir $(dir $(OUTPUT)) --rust

extract-all: $(OUTPUT)
	+$(MAKE) -f extract.Makefile extract

snapshot: extract-all
	cp _output/{cbordetveraux,cbordetver,commonpulse,coseformat}.rs ../rust/src

build-rust: extract-all
	cd ../rust && cargo build

.PHONY: build-rust extract-all all

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
