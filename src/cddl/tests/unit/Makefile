# Note: no postlude added to these tests.

.NOTINTERMEDIATE:
.DELETE_ON_ERROR:

all: all-c
all: all-run

ODIR := _output

ALL_CDDLS = $(wildcard *.cddl)
ALL_FSTS = $(patsubst %.cddl,$(ODIR)/%.fst,$(ALL_CDDLS))
ALL_CHECKED = $(patsubst %.cddl,$(ODIR)/%.fst.checked,$(ALL_CDDLS))
ALL_C_FILES = $(patsubst %.cddl,$(ODIR)/%.c,$(ALL_CDDLS))

RUN += $(patsubst Test_%.c,%,$(wildcard Test_*.c))
RUN += $(patsubst Test_%.cpp,%,$(wildcard Test_*.cpp))

.PHONY: all-fst
all-fst: $(ALL_FSTS)

.PHONY: all-checked
all-checked: $(ALL_CHECKED)

.PHONY: all-c
all-c: $(ALL_C_FILES)

EVERPARSE_SRC_PATH = $(realpath ../../..)

$(ODIR)/%.fst: %.cddl
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --mname "$(patsubst %.cddl,%,$<)" --odir $(ODIR) --fstar_only

$(ODIR)/%.o: $(ODIR)/%.c
	$(CC) -O3 -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I _output --std=gnu2x $(CFLAGS) -c $< -o $@

EVERPARSE_PATH = $(realpath $(EVERPARSE_SRC_PATH)/..)
OUTPUT_DIRECTORY := _output
SRC_PATHS += $(OUTPUT_DIRECTORY)
INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/tool $(EVERPARSE_PATH)/lib/evercddl/lib $(EVERPARSE_PATH)/lib/evercddl/plugin $(EVERPARSE_SRC_PATH)/cbor/pulse $(EVERPARSE_SRC_PATH)/cddl/pulse $(OUTPUT_DIRECTORY)

ALREADY_CACHED := ,*
FSTAR_OPTIONS += --load_cmxs evercddl_lib --load_cmxs evercddl_plugin
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend
FSTAR_DEP_OPTIONS := --extract '*,-FStar,-Pulse,-CBOR,-CDDL'
FSTAR_FILES := $(ALL_FSTS)

CBOR_KRML_MODULES += CBOR.Spec.Constants
CBOR_KRML_MODULES += CBOR.Pulse.API.Det.Type
CBOR_KRML_MODULES += CBOR.Pulse.API.Det.C

CBOR_KRML_MODULES += CDDL.Pulse.Misc
CBOR_KRML_MODULES += CDDL.Spec.Misc
CBOR_KRML_MODULES += CDDL.Pulse.MapGroup
CBOR_KRML_MODULES += CDDL.Pulse.Parse.MapGroup
CBOR_KRML_MODULES += CDDL.Pulse.Serialize.MapGroup
# CBOR_KRML_MODULES += CDDL.Pulse.ArrayGroup
CBOR_KRML_MODULES += CDDL.Pulse.Parse.ArrayGroup
# CBOR_KRML_MODULES += CDDL.Pulse.Serialize.ArrayGroup
CBOR_KRML_MODULES += CDDL.Pulse.Types

CBOR_KRML_MODULES += Pulse.Lib.Slice

CBOR_KRML_MODULES += FStar.Pervasives
CBOR_KRML_MODULES += FStar.Pervasives.Native

FSTAR_DEP_OPTIONS += $(addprefix --extract +,$(CBOR_KRML_MODULES))

clean_rules += clean-tinycbor clean-QCBOR clean-c clean-output

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

KRML_OPTS += -warn-error @4@6

KRML=$(KRML_HOME)/krml -fstar $(FSTAR_EXE) $(KRML_OPTS)

CBOR_KRML_FILES = $(patsubst %,%.krml,$(subst .,_,$(CBOR_KRML_MODULES)))

$(OUTPUT_DIRECTORY)/%.c: $(OUTPUT_DIRECTORY)/%.krml $(addprefix $(OUTPUT_DIRECTORY)/,$(CBOR_KRML_FILES))
	$(KRML) -fnoshort-enums \
	 -bundle 'CBOR.Spec.Constants+CBOR.Pulse.API.Det.Type+CBOR.Pulse.API.Det.C=CBOR.\*[rename=CBORDetAPI]' \
	 -bundle '$*=*' \
	 -add-include '"CBORDetAbstract.h"' \
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

QCBOR/libqcbor.a: QCBOR
	$(MAKE) -C QCBOR

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
$(ODIR)/Test_%.exe: $(ODIR)/Test_%.o $(ODIR)/$$(call remove__,%).o QCBOR/libqcbor.a tinycbor-build/libtinycbor.a
	$(CC) -O3 -o $@ $^ $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c/CBORDet.o QCBOR/libqcbor.a tinycbor-build/libtinycbor.a -lm

$(ODIR)/Test_%.o: Test_%.c $(ODIR)/$$(call remove__,%).c
	$(CC) -O3 -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I _output --std=gnu2x $(CFLAGS) -c $< -o $@

$(ODIR)/Test_%.o: Test_%.cpp $(ODIR)/$$(call remove__,%).c tinycbor-build
	$(CC) -O3 -I $(EVERPARSE_SRC_PATH)/cbor/pulse/det/c -I tinycbor-build/src -I tinycbor-build -I _output --std=c++2a $(CFLAGS) -c $< -o $@

%.run: $(ODIR)/Test_%.exe
	./$<

qcbor_bench: qcbor_bench.c QCBOR/libqcbor.a
	$(CC) $(CFLAGS) -O3 -o $@ $< QCBOR/libqcbor.a -lm

run-qcbor_bench: qcbor_bench
	./$<

# all: run

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
