# Note: no postlude added to these tests.

all: all-c
all: all-build
all: all-run
all: run-qcbor_bench

.NOTINTERMEDIATE:
.DELETE_ON_ERROR:

ODIR := _output

ALL_CDDLS = $(wildcard *.cddl)
ALL_FSTS = $(patsubst %.cddl,$(ODIR)/%.fst,$(ALL_CDDLS))
ALL_CHECKED = $(patsubst %.cddl,$(ODIR)/%.fst.checked,$(ALL_CDDLS))
ALL_C_FILES = $(patsubst %.cddl,$(ODIR)/%.c,$(ALL_CDDLS))

RUN += $(patsubst Test_%.c,%,$(wildcard Test_*.c))
RUN += $(patsubst Test_%.cpp,%,$(wildcard Test_*.cpp))

# QCBOR does not compile with mingw64, because it hardcodes GNU `ar` instead of $(AR)
ifeq ($(OS),Windows_NT)
  RUN := $(filter-out BenchArray__Interop1 BenchArray__Interop2 BenchFlat BenchMap,$(RUN))
endif

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

.PHONY: all-fst
all-fst: $(ALL_FSTS)

.PHONY: all-checked
all-checked: $(ALL_CHECKED)

.PHONY: all-c
all-c: $(ALL_C_FILES)

EVERPARSE_SRC_PATH = $(realpath ../../..)

$(ODIR)/%.fst: %.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname "$(patsubst %.cddl,%,$<)" --odir $(ODIR) --fstar_only $(CDDL_ADMIT)

$(ODIR)/%.o: $(ODIR)/%.c
	$(CC) -O3 -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I _output --std=gnu2x $(CFLAGS) -c $< -o $@

EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
SRC_PATHS += $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := ,*
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_FILES := $(ALL_FSTS)

# One whole-program extraction per .cddl: each generated module is its own
# program, so the Custard run below is driven by the pattern rule rather than
# by common.Makefile's single $(CUSTARD_KRML) rule.  The module under
# extraction is added as an entry per target.  The two abstract CBOR types
# come from the -add-include'd CBORDetType.h, so Custard must not typedef them
# itself.
CUSTARD_BACKEND := KrmlC
CUSTARD_EXTERN_TYPES := CBOR.Pulse.API.Det.Type.cbor_det_t
CUSTARD_EXTERN_TYPES += CBOR.Pulse.API.Det.Type.cbor_det_map_entry_t

clean_rules += clean-tinycbor clean-QCBOR clean-c clean-output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

$(OUTPUT_DIRECTORY)/%.krml: $(OUTPUT_DIRECTORY)/%.fst.checked $(ALL_CHECKED_FILES)
	$(call msg, "CUSTARD", $*)
	$(Q)$(CUSTARD) --custard_entry_module $* $(OUTPUT_DIRECTORY)/$*.fst -o $@

# A single bundle, so that every module gets one self-contained header.  The
# CBOR API is nothing but external declarations here -- its definitions come
# from the CBORDet.o these tests link against -- so there is no reason to
# package it separately, and a separate generated CBORDetAPI.h would be
# written once per .cddl into the shared output directory, each run keeping
# only the subset its own module happened to reach.  Drivers that call the
# CBOR API directly include the library's own CBORDet.h instead.
$(OUTPUT_DIRECTORY)/%.c: $(OUTPUT_DIRECTORY)/%.krml
	$(KRML) -fnoshort-enums \
	 -bundle '$*=*' \
	 -skip-makefiles \
	 -add-include '"CBORDetType.h"' -no-prefix CBOR.Pulse.API.Det.Dummy \
	 -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type \
	 -no-prefix CBOR.Spec.Constants -skip-compilation $^ \
	 -tmpdir $(OUTPUT_DIRECTORY)

# $(OUTPUT_DIRECTORY)/test.exe: $(OUTPUT_DIRECTORY)/CDDLExtractionTest.o client.c
# 	$(CC) $(CFLAGS) -Wall -o $@ $^ $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.o -I $(OUTPUT_DIRECTORY) -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c

# extract: $(OUTPUT_DIRECTORY)/test.exe

# test: extract
# 	$(OUTPUT_DIRECTORY)/test.exe

# .PHONY: extract test

remove__ = $(firstword $(subst __, ,$1))

.SECONDEXPANSION:

CFLAGS += -I QCBOR/inc -g

QCBOR:
	rm -rf $@.tmp
	git clone "https://github.com/laurencelundblade/QCBOR" $@.tmp
	cd $@.tmp && git checkout 83c4af09d3752afa64ae66e2a3382192bf682541
	mv $@.tmp $@

include qcbor.Makefile

tinycbor:
	rm -rf $@.tmp
	git clone "https://github.com/intel/tinycbor" $@.tmp
	cd $@.tmp && git checkout 45e4641059709862b4e46f3608d140337566334b
	mv $@.tmp $@

tinycbor-build: tinycbor
	cmake -S tinycbor -B tinycbor-build

tinycbor-build/libtinycbor.a: tinycbor-build
	$(MAKE) -C tinycbor-build

# Some tests require libqcbor, we just add it to this invocation for all tests.
# And libqcbor requires -lm (though we could disable that)
# Disable qcbor on Cygwin with mingw64
ifneq ($(OS),Windows_NT)
with_qcbor := QCBOR/libqcbor.a
endif
$(ODIR)/Test_%.exe: $(ODIR)/Test_%.o $(ODIR)/$$(call remove__,%).o $(with_qcbor) tinycbor-build/libtinycbor.a
	$(CC) -O3 -o $@ $^ $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.o -lm

$(ODIR)/Test_%.o: Test_%.c $(ODIR)/$$(call remove__,%).c
	$(CC) -O3 -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I _output --std=gnu2x $(CFLAGS) -c $< -o $@

$(ODIR)/Test_%.o: Test_%.cpp $(ODIR)/$$(call remove__,%).c tinycbor-build
	$(CC) -O3 -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I tinycbor-build/src -I tinycbor-build -I _output --std=c++2a $(CFLAGS) -c $< -o $@

%.run: $(ODIR)/Test_%.exe
	./$<

ifeq ($(OS),Windows_NT)
run-qcbor_bench:
else
qcbor_bench: qcbor_bench.c QCBOR/libqcbor.a
	$(CC) $(CFLAGS) -O3 -o $@ $< QCBOR/libqcbor.a -lm

run-qcbor_bench: qcbor_bench
	./$<
endif

# all: run

.PHONY: run-qcbor_bench

.PHONY: all-build
all-build: $(patsubst %,$(ODIR)/Test_%.exe,$(RUN))

.PHONY: all-run
all-run: $(patsubst %,%.run,$(RUN))

clean-tinycbor:
	rm -rf tinycbor tinycbor-build

.PHONY: clean-tinycbor

clean-QCBOR:
	rm -rf QCBOR

.PHONY: clean-QCBOR

clean-c:
	rm -f *.o qcbor_bench $(ODIR)/*.o $(ODIR)/*.exe

.PHONY: clean-c

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
