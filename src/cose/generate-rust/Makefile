all: extract-all

EVERPARSE_SRC_PATH = $(realpath ../..)

OUTPUT=_output/COSE.Format.fst

$(OUTPUT): ../cose-sign.cddl ../../cddl/spec/postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname COSE.Format --odir $(dir $(OUTPUT)) --rust --fstar_only

extract-all: $(OUTPUT)
	+$(MAKE) -f extract.Makefile extract

SNAPSHOT_FILES=cbordetveraux cbordetver commonpulse coseformat
SNAPSHOT_FILES_RS=$(addsuffix .rs,$(SNAPSHOT_FILES))
OUTPUT_SNAPSHOT_FILES_RS=$(addprefix _output/,$(SNAPSHOT_FILES_RS))

snapshot: extract-all
	cp $(OUTPUT_SNAPSHOT_FILES_RS) ../rust/src/

.PHONY: extract-all snapshot all

%.diff: extract-all
	diff ../rust/src/$(basename $@) _output/$(basename $@)

.PHONY: %.diff

test: extract-all
ifeq ($(EVERPARSE_NO_DIFF),) # Set this variable to disable diffs
test: $(addsuffix .diff,$(SNAPSHOT_FILES_RS))
endif

.PHONY: test

# Uncomment if you want to edit the produced F* file
include extract.Makefile
