all: build-rust

EVERPARSE_SRC_PATH = $(realpath ../../..)

OUTPUT=_output/CDDLTest.Test.fst

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

$(OUTPUT): test.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $(dir $(OUTPUT)) --rust --fstar_only $(CDDL_ADMIT)

RUST_MODULES := cbordetver cbordetveraux cddlextractiontest

extract-all: $(OUTPUT)
	+$(MAKE) -f extract.Makefile extract
	for f in $(RUST_MODULES) ; do cp _output/$$f.rs src/ ; done

build-rust: extract-all
	cargo build

.PHONY: build-rust extract-all all

clean:
	cargo clean
	+$(MAKE) -f extract.Makefile clean
	for f in $(RUST_MODULES) ; do rm -f src/$$f.rs ; done

.PHONY: clean

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
