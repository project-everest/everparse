# everparse-asn1: build and tests.
# Prerequisites: OCaml with dune (e.g. the opam switch of EverParse), and
# the verified ASN.1 Pulse library (`make -C ../pulse verify`).

all: test

EVERPARSE_HOME ?= $(realpath ../../..)
FSTAR_EXE ?= $(EVERPARSE_HOME)/opt/FStar/out/bin/fstar.exe
export EVERPARSE_HOME FSTAR_EXE
DUNE ?= dune
CC ?= cc
TEST_CFLAGS := -std=c11 -Wall -Wextra -Werror -Wno-type-limits -Wno-unused-variable -O1

TOOL := ocaml/_build/default/everparse-asn1/Main.exe
OUT := _output

$(TOOL): $(wildcard ocaml/dune-project ocaml/everparse-asn1/*.ml ocaml/everparse-asn1/*.mll ocaml/everparse-asn1/dune)
	cd ocaml && $(DUNE) build

build: $(TOOL)

# C round trip on a generated API
$(OUT)/small/Small.c: tests/Small.asn $(TOOL)
	$(TOOL) --odir $(OUT)/small $<

$(OUT)/small_test.exe: $(OUT)/small/Small.c tests/small_test.c
	$(CC) $(TEST_CFLAGS) -I $(OUT)/small -o $@ $^

test-small: $(OUT)/small_test.exe
	$<

# The generated schemas agree with the hand translations of difftest/schemas
GOLDEN := DiffConstructed DiffSet DiffConstraints

$(OUT)/golden/%.fst: ../difftest/schemas/%.asn $(TOOL)
	$(TOOL) --fstar_only --odir $(OUT)/golden $<

test-golden: $(addprefix $(OUT)/golden/,$(addsuffix .fst,$(GOLDEN)))
	cd tests && $(FSTAR_EXE) --smt $(EVERPARSE_HOME)/opt/z3/z3-5.3.0 --z3version 5.3.0 \
	  --include $(EVERPARSE_HOME)/lib/everparse/lowparse --include $(EVERPARSE_HOME)/src/ASN1 --include $(CURDIR)/$(OUT)/golden \
	  --already_cached '*,-Golden,-DiffConstructed,-DiffSet,-DiffConstraints' Golden.fst

test: test-golden test-small

clean:
	rm -rf $(OUT)
	cd ocaml && $(DUNE) clean

.PHONY: all build test test-small test-golden clean
.PRECIOUS: $(OUT)/small/Small.c $(OUT)/golden/%.fst
