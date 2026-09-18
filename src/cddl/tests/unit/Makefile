# Note: no postlude added to these tests.

all: all-c
all: all-build
all: all-run
all: run-qcbor_bench

.NOTINTERMEDIATE:
.DELETE_ON_ERROR:

ODIR := _output

EVERPARSE_SRC_PATH = $(realpath ../../..)

# --------------------------------------------------------------- Custard ---
#
# Custard (F*'s WIP extraction backend, see ../../README.custard.md) emits the
# whole program as one translation unit per entry-point set, with the det CBOR
# API folded in -- so there is no CBORDetAPI.h on an include path and no
# CBORDet.o to link.  Everything downstream of the generated .c is identical
# between the two backends, so rather than duplicate the nine driver rules we
# just point them at a different directory and drop the two karamel-only
# ingredients.
include $(EVERPARSE_SRC_PATH)/custard-detect.Makefile

ifeq (1,$(CUSTARD))
  CDIR := $(ODIR)/custard
  # The shim in $(CDIR) supplies CBORDetAPI.h; the snapshot's real one must
  # not be on the path or it would shadow it and redeclare the folded-in API.
  TEST_INCLUDES := -I $(CDIR) -DEVERPARSE_CUSTARD
  CBORDET_O :=
else
  CDIR := $(ODIR)
  TEST_INCLUDES := -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I $(CDIR)
  CBORDET_O := $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.o
endif

ALL_CDDLS = $(wildcard *.cddl)
ALL_FSTS = $(patsubst %.cddl,$(ODIR)/%.fst,$(ALL_CDDLS))
ALL_CHECKED = $(patsubst %.cddl,$(ODIR)/%.fst.checked,$(ALL_CDDLS))
ALL_C_FILES = $(patsubst %.cddl,$(CDIR)/%.c,$(ALL_CDDLS))

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

$(ODIR)/%.fst: %.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname "$(patsubst %.cddl,%,$<)" --odir $(ODIR) --fstar_only $(CDDL_ADMIT)

$(CDIR)/%.o: $(CDIR)/%.c
	$(CC) -O3 $(TEST_INCLUDES) --std=gnu2x $(CFLAGS) -c $< -o $@

EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
SRC_PATHS += $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := ,*
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar,-Pulse,-CBOR,-CDDL'
FSTAR_FILES := $(ALL_FSTS)

CBOR_KRML_MODULES += CBOR.Spec.Constants
CBOR_KRML_MODULES += CBOR.Pulse.API.Det.Type
CBOR_KRML_MODULES += CBOR.Pulse.API.Det.C
CBOR_KRML_MODULES += CBOR.Pulse.API.Det.Dummy

CBOR_KRML_MODULES += CDDL.Pulse.Misc
CBOR_KRML_MODULES += CDDL.Spec.Misc
CBOR_KRML_MODULES += CDDL.Pulse.MapGroup
CBOR_KRML_MODULES += CDDL.Pulse.Parse.MapGroup
CBOR_KRML_MODULES += CDDL.Pulse.Serialize.Gen.MapGroup.ZeroOrMore
# CBOR_KRML_MODULES += CDDL.Pulse.ArrayGroup
CBOR_KRML_MODULES += CDDL.Pulse.Parse.ArrayGroup
# CBOR_KRML_MODULES += CDDL.Pulse.Serialize.ArrayGroup
CBOR_KRML_MODULES += CDDL.Pulse.Types

CBOR_KRML_MODULES += Pulse.Lib.Pervasives
CBOR_KRML_MODULES += Pulse.Lib.Slice

CBOR_KRML_MODULES += FStar.Pervasives
CBOR_KRML_MODULES += FStar.Pervasives.Native

FSTAR_DEP_OPTIONS += $(addprefix --extract +,$(CBOR_KRML_MODULES))

clean_rules += clean-tinycbor clean-QCBOR clean-c clean-output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) $(KRML_OPTS)

CBOR_KRML_FILES = $(patsubst %,%.krml,$(subst .,_,$(CBOR_KRML_MODULES)))

# The karamel-native rule.  Guarded so that under CUSTARD=1 the only way to
# make a .c is the Custard rule below -- CDIR differs, so they cannot collide,
# but leaving both enabled would let a stale karamel .c satisfy a Custard
# prerequisite if the directories were ever unified again.
ifneq (1,$(CUSTARD))
$(OUTPUT_DIRECTORY)/%.c: $(OUTPUT_DIRECTORY)/%.krml $(addprefix $(OUTPUT_DIRECTORY)/,$(CBOR_KRML_FILES))
	$(KRML) -fnoshort-enums \
	 -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C+FStar.Pervasives.Native=CBOR.\*[rename=CBORDetAPI]' \
	 -bundle '$*=*' \
	 -skip-makefiles \
	 -add-include '"CBORDetType.h"' -no-prefix CBOR.Pulse.API.Det.Dummy \
	 -no-prefix CBOR.Pulse.API.Det.C -no-prefix CBOR.Pulse.API.Det.Type \
	 -no-prefix CBOR.Spec.Constants -skip-compilation $^ \
	 -tmpdir $(OUTPUT_DIRECTORY)
endif

# Custard: one translation unit per .cddl, whose entry modules are the union
# of the `+` lists of the two -bundle flags above -- the module itself plus
# the det CBOR API.  That is the same program stated the other way round.
CUSTARD_C_ENTRY_MODULES = $* $(CUSTARD_CBOR_DET_ENTRY_MODULES)

include $(EVERPARSE_SRC_PATH)/cddl/tests/custard.Makefile

$(ODIR)/custard/%.c: $(ODIR)/%.fst.checked
	mkdir -p $(dir $@)
	$(CUSTARD_FSTAR) $(CUSTARD_C_FLAGS) $(ODIR)/$*.fst -o $(CURDIR)/$@
	$(call custard-cbor-shim-empty,$(dir $@))

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
$(CDIR)/Test_%.exe: $(CDIR)/Test_%.o $(CDIR)/$$(call remove__,%).o $(with_qcbor) tinycbor-build/libtinycbor.a
	$(CC) -O3 -o $@ $^ $(CBORDET_O) -lm

$(CDIR)/Test_%.o: Test_%.c $(CDIR)/$$(call remove__,%).c
	$(CC) -O3 $(TEST_INCLUDES) --std=gnu2x $(CFLAGS) -c $< -o $@

$(CDIR)/Test_%.o: Test_%.cpp $(CDIR)/$$(call remove__,%).c tinycbor-build
	$(CC) -O3 $(TEST_INCLUDES) -I tinycbor-build/src -I tinycbor-build --std=c++2a $(CFLAGS) -c $< -o $@

%.run: $(CDIR)/Test_%.exe
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
all-build: $(patsubst %,$(CDIR)/Test_%.exe,$(RUN))

.PHONY: all-run
all-run: $(patsubst %,%.run,$(RUN))

clean-tinycbor:
	rm -rf tinycbor tinycbor-build

.PHONY: clean-tinycbor

clean-QCBOR:
	rm -rf QCBOR

.PHONY: clean-QCBOR

clean-c:
	rm -f *.o qcbor_bench $(ODIR)/*.o $(ODIR)/*.exe $(ODIR)/custard/*.o $(ODIR)/custard/*.exe

.PHONY: clean-c

clean-output:
	rm -rf $(OUTPUT_DIRECTORY)

.PHONY: clean-output
