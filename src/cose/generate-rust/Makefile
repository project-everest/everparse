all: extract-all

EVERPARSE_SRC_PATH = $(realpath ../..)

include $(EVERPARSE_SRC_PATH)/custard-detect.Makefile

OUTPUT=_output/COSE.Format.fst

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

$(OUTPUT): ../cose-sign.cddl ../../cddl/spec/postlude.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname COSE.Format --odir $(dir $(OUTPUT)) --rust --fstar_only $(CDDL_ADMIT)

extract-krml: $(OUTPUT)
	+$(MAKE) -f extract.Makefile extract-krml

# CUSTARD defaults to 1 when the F* in use has Custard and to 0 otherwise;
# see custard-detect.Makefile.  `extract' in extract.Makefile already depends
# on `extract-krml' there, so the karamel-native leg is unchanged.
extract-all: $(OUTPUT)
	+$(MAKE) -f extract.Makefile $(if $(filter 1,$(CUSTARD)),extract-custard,extract)

SNAPSHOT_FILES=cbordetveraux cbordetver commonpulse coseformat
SNAPSHOT_FILES_RS=$(addsuffix .rs,$(SNAPSHOT_FILES))
OUTPUT_SNAPSHOT_FILES_RS=$(addprefix _output/,$(SNAPSHOT_FILES_RS))

ifeq (1,$(CUSTARD))
snapshot: extract-all
	cp $(OUTPUT_SNAPSHOT_FILES_RS) ../rust/src/
else
# ../rust/src holds Custard output; karamel's would not be an update of it.
snapshot: extract-all
	@echo 'ERROR: ../rust/src holds Custard output, and this F* has no Custard.' >&2
	@echo '       Rebuild F* from the gebner_custard branch (FStarLang/FStar#4395);' >&2
	@echo '       see ../README.custard.md.' >&2
	@false
endif

.PHONY: extract-all extract-krml snapshot all

%.diff: extract-all
	diff ../rust/src/$(basename $@) _output/$(basename $@)

.PHONY: %.diff

test: extract-all
ifeq (1,$(CUSTARD))
ifeq ($(EVERPARSE_CHECK_DIFF),1) # Set this variable to enable diffs
test: $(addsuffix .diff,$(SNAPSHOT_FILES_RS))
endif
else
test:
	@echo 'NOTE: extracted with karamel; not diffed against ../rust/src, which'
	@echo '      holds Custard output.  See ../README.custard.md.'
endif

.PHONY: test

# Uncomment if you want to edit the produced F* file
include extract.Makefile
