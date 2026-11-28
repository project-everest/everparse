# everparse-asn1 ($(EVERPARSE_HOME)/bin/everparse-asn1.exe): generate C
# from test schemas, then compile and run C tests against it.  F* and Z3
# are found by the tool, or given with FSTAR_EXE and Z3_EXE.

all: test

EVERPARSE_HOME ?= $(realpath ../../../../..)
CC ?= cc
TEST_CFLAGS := -std=c11 -Wall -Wextra -Werror -Wno-type-limits -Wno-unused-variable -O1

comma := ,
empty :=
space := $(empty) $(empty)
TOOL_EXE := $(EVERPARSE_HOME)/bin/everparse-asn1.exe
TOOL = $(TOOL_EXE) $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(Z3_EXE),--z3 "$(Z3_EXE)")
OUT := _output

# C round trip on a generated API
$(OUT)/small/Small.c: Small.asn $(TOOL_EXE)
	$(TOOL) --odir $(OUT)/small --root Msg,Names,Wrapper $<

$(OUT)/small_test.exe: $(OUT)/small/Small.c small_test.c
	$(CC) $(TEST_CFLAGS) -I $(OUT)/small -o $@ $^

test-small: $(OUT)/small_test.exe
	$<

# IMPORTS, value assignments, ANY DEFINED BY tables, CONTAINING, DEFAULT
# under an EXPLICIT tag, and KEEP-BYTES
$(OUT)/x509lite/X509Lite.c: X509Lite.asn X509LiteBase.asn $(TOOL_EXE)
	$(TOOL) --lax_size_of --odir $(OUT)/x509lite --root Cert,Extension,BasicConstraints X509Lite.asn X509LiteBase.asn

$(OUT)/x509lite_test.exe: $(OUT)/x509lite/X509Lite.c x509lite_test.c
	$(CC) $(TEST_CFLAGS) -I $(OUT)/x509lite -o $@ $^

test-x509lite: $(OUT)/x509lite_test.exe
	$<

# Open ranges and unions, DEFAULT strings and BIT STRINGs, DEFINED-BY keys
# of string and INTEGER types, EXTERNAL and EMBEDDED PDV, and KEEP-BYTES
# under an IMPLICIT tag and on a component
$(OUT)/features/Features.c: Features.asn $(TOOL_EXE)
	$(TOOL) --odir $(OUT)/features --root Rec,Item,Opt,Pdv $<

$(OUT)/features_test.exe: $(OUT)/features/Features.c features_test.c
	$(CC) $(TEST_CFLAGS) -I $(OUT)/features -o $@ $^

test-features: $(OUT)/features_test.exe
	$<

# Value notations, BOOLEAN constraints, WITH COMPONENTS, parameterized
# types (imported), information object classes and table constraints,
# constraint set operations and serial constraints
$(OUT)/features2/Features2.c: Features2.asn Features2Base.asn $(TOOL_EXE)
	$(TOOL) --odir $(OUT)/features2 --root Vals,Derived,PRec,AlgId,Exts,Attr,Alg,More,Outer Features2.asn Features2Base.asn

$(OUT)/features2_test.exe: $(OUT)/features2/Features2.c features2_test.c
	$(CC) $(TEST_CFLAGS) -I $(OUT)/features2 -o $@ $^

test-features2: $(OUT)/features2_test.exe
	$<

# The generated schemas agree with the hand translations of
# ../difftest/schemas (ASN1.DiffTest.*, verified by ../difftest)
GOLDEN := DiffConstructed DiffSet DiffConstraints DiffAny DiffExternal DiffPdv DiffCharStr
DIFFTEST_DIR := $(realpath ../difftest)

$(OUT)/golden/%.fst: $(DIFFTEST_DIR)/schemas/%.asn $(TOOL_EXE)
	$(TOOL) --fstar_only --odir $(OUT)/golden $<

# Golden.fst is checked with the same F* and Z3 as the library
GOLDEN_INCLUDE_PATHS := $(EVERPARSE_HOME)/lib/everparse/lowparse $(EVERPARSE_HOME)/lib/everparse/asn1/spec $(DIFFTEST_DIR) $(CURDIR)/$(OUT)/golden
ifeq ($(OS),Windows_NT)
GOLDEN_INCLUDE_PATHS := $(shell cygpath -m $(GOLDEN_INCLUDE_PATHS))
endif
ALREADY_CACHED := *,-Golden,$(subst $(space),$(comma),$(addprefix -,$(GOLDEN))),
include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile

test-golden: $(addprefix $(OUT)/golden/,$(addsuffix .fst,$(GOLDEN)))
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(addprefix --include ,$(GOLDEN_INCLUDE_PATHS)) \
	  --already_cached '$(ALREADY_CACHED)Prims,FStar' Golden.fst

test: test-golden test-small test-x509lite test-features test-features2

clean:
	rm -rf $(OUT)

.PHONY: all test test-small test-x509lite test-features test-features2 test-golden clean
.PRECIOUS: $(OUT)/small/Small.c $(OUT)/x509lite/X509Lite.c $(OUT)/features/Features.c $(OUT)/features2/Features2.c $(OUT)/golden/%.fst
