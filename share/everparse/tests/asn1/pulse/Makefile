# C tests of the ASN.1 Pulse library (lib/everparse/asn1/pulse): the
# validators of the differential test schemas (ASN1.Pulse.DiffTest.*, on
# the F* schemas of ../difftest) on the test vectors of ../difftest, and
# the parsers and writers of ASN1.Pulse.{ParseTest,RawWriteTest,NamedTest}.
# The modules are extracted to C with Custard (no KaRaMeL).

all: test test-parse test-raw-write test-named test-deep-any

EVERPARSE_HOME ?= $(realpath ../../../../..)
LOWPARSE_HOME = $(EVERPARSE_HOME)/lib/everparse/lowparse
ASN1_HOME = $(EVERPARSE_HOME)/lib/everparse/asn1
DIFFTEST_DIR := $(realpath ../difftest)

INCLUDE_PATHS += $(LOWPARSE_HOME) $(ASN1_HOME)/spec $(ASN1_HOME)/pulse $(DIFFTEST_DIR)

# The library is verified by EverParse (`make asn1`), and the F* schemas
# by ../difftest
ALREADY_CACHED := *,-ASN1.Pulse.DiffTest,-ASN1.Pulse.ParseTest,-ASN1.Pulse.RawWriteTest,-ASN1.Pulse.NamedTest,

include $(EVERPARSE_HOME)/lib/everparse/pulse.Makefile
include $(EVERPARSE_HOME)/lib/everparse/common.Makefile

C_OUTPUT_DIR := _output
CUSTARD_C_FLAGS := --codegen C --custard_monomorphize_types true

$(C_OUTPUT_DIR)/%.c: %.fst.checked
	mkdir -p $(C_OUTPUT_DIR)
	$(FSTAR) $(CUSTARD_C_FLAGS) --custard_entry_module $* $*.fst -o $@

CC ?= cc
# -Wno-type-limits: the extracted length decoder keeps range checks that are
# tautologies on unsigned C types; -Wno-unused-variable: content validators
# that ignore their input (e.g. NULL) leave the slice split by the length
# check unused
TEST_CFLAGS := -std=c11 -Wall -Wextra -Werror -Wno-type-limits -Wno-unused-variable -O1

# The differential test validators: test cases, and the C files that
# EverParse's src/ASN1/pulse uses for its oracle tests
include difftest.Makefile

extract: $(addprefix $(C_OUTPUT_DIR)/,$(addsuffix .c,$(DIFFTEST_MODULES)))

.SECONDEXPANSION:
$(C_OUTPUT_DIR)/test_%.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.DiffTest.$$($$*.module).c test/driver.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) \
	  -DHEADER='"ASN1.Pulse.DiffTest.$($*.module).h"' \
	  -DVALIDATE=ASN1_Pulse_DiffTest_$($*.module)_$($*.entry) \
	  -o $@ $< test/driver.c

# The validators against the committed vectors and their expected verdicts
test-%: $(C_OUTPUT_DIR)/test_%.exe
	python3 test/vectors.py --type $($*.type) $(DIFFTEST_DIR)/vectors/$($*.vectors) | $<

test: $(addprefix test-,$(C_TESTS))

# Zero-copy parsers (ASN1.Pulse.Parser) on hand-written encodings
$(C_OUTPUT_DIR)/parse_test.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.ParseTest.c test/parse_test.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) -o $@ $< test/parse_test.c

test-parse: $(C_OUTPUT_DIR)/parse_test.exe
	$<

# JIT writers (ASN1.Pulse.JitWriter, ASN1.Pulse.RawJitWriter): write raw
# values with no precondition, checking them against the schema
$(C_OUTPUT_DIR)/raw_write_test.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.RawWriteTest.c test/raw_write_test.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) -o $@ $< test/raw_write_test.c

test-raw-write: $(C_OUTPUT_DIR)/raw_write_test.exe
	$<

# Named C types through impl descriptors (ASN1.Pulse.NamedTest)
$(C_OUTPUT_DIR)/named_test.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.NamedTest.c test/named_test.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) -o $@ $< test/named_test.c

test-named: $(C_OUTPUT_DIR)/named_test.exe
	$<

# Deeply nested ANY (constant stack: run with a 64 KiB stack limit)
DEEP_ANY_DEPTH := 4000
test-deep-any: $(C_OUTPUT_DIR)/test_Any_AnyT.exe
	python3 test/deep_any.py $(DEEP_ANY_DEPTH) | (ulimit -s 64 && $<)

clean_rules += clean-output

clean-output:
	rm -rf $(C_OUTPUT_DIR)

.PRECIOUS: $(C_OUTPUT_DIR)/%.c $(C_OUTPUT_DIR)/%.h $(C_OUTPUT_DIR)/test_%.exe $(C_OUTPUT_DIR)/parse_test.exe $(C_OUTPUT_DIR)/raw_write_test.exe $(C_OUTPUT_DIR)/named_test.exe
.PHONY: all extract test test-parse test-raw-write test-named test-deep-any clean-output
