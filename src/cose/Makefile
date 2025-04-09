all: build interop

EVERPARSE_SRC_PATH = $(realpath ..)

OUTPUT_DIRECTORY=_output
OUTPUT=$(OUTPUT_DIRECTORY)/COSE.Format.fst

$(OUTPUT): cose.cddl ../cddl/spec/postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname COSE.Format --odir $(dir $(OUTPUT))
	cp extract0.Makefile $(OUTPUT_DIRECTORY)/Makefile

build:
	+$(MAKE) -C snapshot

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
snapshot: $(OUTPUT)
	+$(MAKE) -f extract.Makefile snapshot

.PHONY: snapshot

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
