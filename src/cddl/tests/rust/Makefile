all: build-rust

EVERPARSE_SRC_PATH := $(realpath ../../..)
include $(EVERPARSE_SRC_PATH)/windows.Makefile

OUTPUT=_output/CDDLTest.Test.fst

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

$(OUTPUT): test.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $(dir $(OUTPUT)) --rust --fstar_only $(CDDL_ADMIT)

RUST_MODULES := cbordetver cbordetveraux cddlextractiontest

# The Rust leg is Custard --custard_backend KrmlRust followed by karamel; only
# the F* -> .krml step changes, so the same karamel bundles produce the same
# three modules and everything downstream is untouched.
include $(EVERPARSE_SRC_PATH)/custard-detect.Makefile

ifeq (1,$(CUSTARD))
  EXTRACT_TARGET := extract-custard
else
  EXTRACT_TARGET := extract
endif

extract-all: $(OUTPUT)
	+$(MAKE) -f extract.Makefile $(EXTRACT_TARGET)
	for f in $(RUST_MODULES) ; do cp _output/$$f.rs src/ ; done

extract-all-custard: $(OUTPUT)
	+$(MAKE) -f extract.Makefile extract-custard
	for f in $(RUST_MODULES) ; do cp _output/$$f.rs src/ ; done

.PHONY: extract-all-custard

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
