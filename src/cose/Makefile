all: build

EVERPARSE_SRC_PATH = $(realpath ..)

OUTPUT_DIRECTORY=_output
OUTPUT=$(OUTPUT_DIRECTORY)/COSE.Format.fst

$(OUTPUT): cose.cddl ../cddl/spec/postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname COSE.Format --odir $(dir $(OUTPUT))
	cp extract0.Makefile $(OUTPUT_DIRECTORY)/Makefile

build-c:
	+$(MAKE) -C c

.PHONY: build-c

build-rust:
	cd rust && cargo build

.PHONY: build-rust

build: build-c build-rust

.PHONY: build

.PHONY: all

test-extract: $(OUTPUT)
	+$(MAKE) -f extract.Makefile test

.PHONY: test-interop
test-interop: build
	+$(MAKE) -C interop

test: test-extract test-interop

.PHONY: test-extract test

# This rule is incompatible with `test-extract`
snapshot: snapshot-c snapshot-rust

.PHONY: snapshot

snapshot-c: $(OUTPUT)
	+$(MAKE) -f extract.Makefile snapshot

.PHONY: snapshot-c

snapshot-rust: $(OUTPUT)
	+$(MAKE) -C generate-rust snapshot

.PHONY: snapshot-c

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
