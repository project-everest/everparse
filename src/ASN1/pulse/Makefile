all: verify

EVERPARSE_HOME = $(realpath ../../..)
LOWPARSE_HOME = $(EVERPARSE_HOME)/lib/everparse/lowparse

INCLUDE_PATHS += $(LOWPARSE_HOME) $(realpath ..)

ALREADY_CACHED := *,-ASN1.Pulse,
FSTAR_OPTIONS += --ext optimize_let_vc

include $(EVERPARSE_HOME)/lib/everparse/pulse.Makefile
include $(EVERPARSE_HOME)/lib/everparse/common.Makefile

# Custard direct-to-C extraction (no KaRaMeL)
C_OUTPUT_DIR := _output
CUSTARD_C_FLAGS := --codegen C --custard_monomorphize_types true

$(C_OUTPUT_DIR)/%.c: %.fst.checked
	mkdir -p $(C_OUTPUT_DIR)
	$(FSTAR) $(CUSTARD_C_FLAGS) --custard_entry_module $* $*.fst -o $@

# C tests: run each extracted validator against its difftest vectors.
# `test` uses the committed vectors and their expected verdicts; `test-oracle`
# also runs the generated mutations, with the pure F* spec runner's verdicts
# (built by ../difftest) as the oracle.
CC ?= cc
# -Wno-type-limits: the extracted length decoder keeps range checks that are
# tautologies on unsigned C types; -Wno-unused-variable: content validators
# that ignore their input (e.g. NULL) leave the slice split by the length
# check unused
TEST_CFLAGS := -std=c11 -Wall -Wextra -Werror -Wno-type-limits -Wno-unused-variable -O1
DIFFTEST_DIR := ../difftest
DIFFTEST_OUT := $(DIFFTEST_DIR)/out

# For each test <T>: extraction root module ASN1.Pulse.DiffTest.<T>.module,
# vectors file, ASN.1 type, and entry point (validator name in that module)
C_TESTS := Smoke
Smoke.module := Smoke
Smoke.vectors := smoke.json
Smoke.type := DiffSmoke.Smoke
Smoke.entry := validate_smoke

# <T> <module> <vectors> <ASN.1 type> <entry>
define difftest_case
C_TESTS += $(1)
$(1).module := $(2)
$(1).vectors := $(3)
$(1).type := $(4)
$(1).entry := $(5)
endef

$(eval $(call difftest_case,Prim_Bool,Prim,prim.json,DiffPrim.Bool,validate_bool_))
$(eval $(call difftest_case,Prim_Int,Prim,prim.json,DiffPrim.Int,validate_int_))
$(eval $(call difftest_case,Prim_Bits,Prim,prim.json,DiffPrim.Bits,validate_bits))
$(eval $(call difftest_case,Prim_Octets,Prim,prim.json,DiffPrim.Octets,validate_octets))
$(eval $(call difftest_case,Prim_Null,Prim,prim.json,DiffPrim.Null,validate_null_))
$(eval $(call difftest_case,Prim_Oid,Prim,prim.json,DiffPrim.Oid,validate_oid))
$(eval $(call difftest_case,Prim_RelOid,Prim,prim.json,DiffRelOid.RelOid,validate_relOid))
$(eval $(call difftest_case,Prim_Desc,Prim,prim.json,DiffDesc.Desc,validate_desc))
$(eval $(call difftest_case,Prim_Iri,Prim,prim.json,DiffIRI.Iri,validate_iri))
$(eval $(call difftest_case,Prim_RelIri,Prim,prim.json,DiffIRI.RelIri,validate_relIri))
$(eval $(call difftest_case,Prim_Enum,Prim,prim.json,DiffPrim.Enum,validate_enum_))
$(eval $(call difftest_case,Strings_Utf8,Strings,strings.json,DiffStrings.Utf8,validate_utf8))
$(eval $(call difftest_case,Strings_Numeric,Strings,strings.json,DiffStrings.Numeric,validate_numeric))
$(eval $(call difftest_case,Strings_Printable,Strings,strings.json,DiffStrings.Printable,validate_printable))
$(eval $(call difftest_case,Strings_Ia5,Strings,strings.json,DiffStrings.Ia5,validate_ia5))
$(eval $(call difftest_case,Strings_Visible,Strings,strings.json,DiffStrings.Visible,validate_visible))
$(eval $(call difftest_case,Strings_Bmp,Strings,strings.json,DiffStrings.Bmp,validate_bmp))
$(eval $(call difftest_case,Strings_Universal,Strings,strings.json,DiffStrings.Universal,validate_universal))
$(eval $(call difftest_case,Strings_Teletex,Strings,strings.json,DiffStrings.Teletex,validate_teletex))
$(eval $(call difftest_case,Strings_Videotex,Strings,strings.json,DiffVideotex.Videotex,validate_videotex))
$(eval $(call difftest_case,Strings_Graphic,Strings,strings.json,DiffStrings2.Graphic,validate_graphic))
$(eval $(call difftest_case,Strings_General,Strings,strings.json,DiffStrings2.General,validate_general))
$(eval $(call difftest_case,Time_Utc,Time,time.json,DiffTime.Utc,validate_utc))
$(eval $(call difftest_case,Time_Gen,Time,time.json,DiffTime.Gen,validate_gen))
$(eval $(call difftest_case,Time_Date,Time,time.json,DiffTime2.Date,validate_date))
$(eval $(call difftest_case,Time_Tod,Time,time.json,DiffTime2.Tod,validate_tod))
$(eval $(call difftest_case,Time_DateTime,Time,time.json,DiffTime2.DateTime,validate_dateTime))
$(eval $(call difftest_case,Constructed_Seq,Constructed,constructed.json,DiffConstructed.Seq,validate_seq))
$(eval $(call difftest_case,Constructed_IntSeq,Constructed,constructed.json,DiffConstructed.IntSeq,validate_intSeq))
$(eval $(call difftest_case,Constructed_Choice,Constructed,constructed.json,DiffConstructed.Choice,validate_choice))
$(eval $(call difftest_case,Constructed_App,Constructed,constructed.json,DiffConstructed.App,validate_app))
$(eval $(call difftest_case,Constructed_PrivExp,Constructed,constructed.json,DiffConstructed.PrivExp,validate_privExp))
$(eval $(call difftest_case,Constructed_HighCtx,Constructed,constructed.json,DiffConstructed.HighCtx,validate_highCtx))
$(eval $(call difftest_case,Constructed_HighApp,Constructed,constructed.json,DiffConstructed.HighApp,validate_highApp))
$(eval $(call difftest_case,Constructed_Nested,Constructed,constructed.json,DiffConstructed.Nested,validate_nested))
$(eval $(call difftest_case,Constructed_OctetsSet,Constructed,constructed.json,DiffConstructed.OctetsSet,validate_octetsSet))
$(eval $(call difftest_case,Constraints_Sized,Constraints,constraints.json,DiffConstraints.Sized,validate_sized))
$(eval $(call difftest_case,Constraints_Byte,Constraints,constraints.json,DiffConstraints.Byte,validate_byte))
$(eval $(call difftest_case,Constraints_NonEmptySeqOf,Constraints,constraints.json,DiffConstraints.NonEmptySeqOf,validate_nonEmptySeqOf))
$(eval $(call difftest_case,Constraints_NonEmptySetOf,Constraints,constraints.json,DiffConstraints.NonEmptySetOf,validate_nonEmptySetOf))
$(eval $(call difftest_case,Set_Set,Set,set.json,DiffSet.Set,validate_set))
$(eval $(call difftest_case,Any_AnyT,Any,any.json,DiffAny.AnyT,validate_anyT))
$(eval $(call difftest_case,Any_AlgId,Any,any.json,DiffAny.AlgId,validate_algId))
$(eval $(call difftest_case,Presentation_Ext,Presentation,presentation.json,DiffExternal.Ext,validate_ext))
$(eval $(call difftest_case,Presentation_Pdv,Presentation,presentation.json,DiffPdv.Pdv,validate_pdv))
$(eval $(call difftest_case,Presentation_CharStr,Presentation,presentation.json,DiffCharStr.CharStr,validate_charStr))

.SECONDEXPANSION:
$(C_OUTPUT_DIR)/test_%.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.DiffTest.$$($$*.module).c test/driver.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) \
	  -DHEADER='"ASN1.Pulse.DiffTest.$($*.module).h"' \
	  -DVALIDATE=ASN1_Pulse_DiffTest_$($*.module)_$($*.entry) \
	  -o $@ $< test/driver.c

test-%: $(C_OUTPUT_DIR)/test_%.exe
	python3 test/vectors.py --type $($*.type) $(DIFFTEST_DIR)/vectors/$($*.vectors) | $<

test-oracle-%: $(C_OUTPUT_DIR)/test_%.exe
	python3 test/vectors.py --type $($*.type) --oracle $(DIFFTEST_OUT)/ours.jsonl \
	  $(DIFFTEST_DIR)/vectors/$($*.vectors) $(DIFFTEST_OUT)/gen/mutations.json | $<

$(addprefix test-oracle-,$(C_TESTS)): $(DIFFTEST_OUT)/ours.jsonl
$(DIFFTEST_OUT)/ours.jsonl: FORCE
	$(MAKE) -C $(DIFFTEST_DIR) out/ours.jsonl
FORCE:

test: $(addprefix test-,$(C_TESTS))
test-oracle: $(addprefix test-oracle-,$(C_TESTS))

# Corpus tests: the X.509 certificate and CRL validators (ASN1.Pulse.X509)
# against the pure F* spec runner on ../evaluation/data
EVALUATION_DIR := ../evaluation
SPEC_RUNNER := $(EVALUATION_DIR)/ASN1_Parser.exe
CORPUS_TESTS := X509 CRL
X509.entry := validate_certificate
CRL.entry := validate_crl

$(C_OUTPUT_DIR)/corpus_%.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.X509.c test/files_driver.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) \
	  -DHEADER='"ASN1.Pulse.X509.h"' \
	  -DVALIDATE=ASN1_Pulse_X509_$($*.entry) \
	  -o $@ $< test/files_driver.c

$(SPEC_RUNNER): FORCE
	$(MAKE) -C .. evaluation/ASN1_Parser.exe

$(EVALUATION_DIR)/data:
	$(MAKE) -C $(EVALUATION_DIR) prepare

test-corpus-%: $(C_OUTPUT_DIR)/corpus_%.exe $(SPEC_RUNNER) $(EVALUATION_DIR)/data
	python3 test/corpus.py --format $* --spec $(SPEC_RUNNER) --exe $< \
	  $(EVALUATION_DIR)/data/$*/positive $(EVALUATION_DIR)/data/$*/negative

test-corpus: $(addprefix test-corpus-,$(CORPUS_TESTS))

# Zero-copy parsers (ASN1.Pulse.Parser) on hand-written encodings
$(C_OUTPUT_DIR)/parse_test.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.ParseTest.c test/parse_test.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) -o $@ $< test/parse_test.c

test-parse: $(C_OUTPUT_DIR)/parse_test.exe
	$<

# Right-to-left writers (ASN1.Pulse.Writer): parse/write round trips
$(C_OUTPUT_DIR)/write_test.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.ParseTest.c test/write_test.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) -o $@ $< test/write_test.c

test-write: $(C_OUTPUT_DIR)/write_test.exe
	$<

# Checked writers (ASN1.Pulse.CheckedWriter): write with the relaxed schema,
# then validate against the original one
$(C_OUTPUT_DIR)/checked_write_test.exe: $(C_OUTPUT_DIR)/ASN1.Pulse.CheckedWriteTest.c test/checked_write_test.c
	$(CC) $(TEST_CFLAGS) -I $(C_OUTPUT_DIR) -o $@ $< test/checked_write_test.c

test-checked-write: $(C_OUTPUT_DIR)/checked_write_test.exe
	$<

# Deeply nested ANY (constant stack: run with a 64 KiB stack limit)
DEEP_ANY_DEPTH := 4000
test-deep-any: $(C_OUTPUT_DIR)/test_Any_AnyT.exe
	python3 test/deep_any.py $(DEEP_ANY_DEPTH) | (ulimit -s 64 && $<)

# Static stack bound: no recursion, and a bounded worst case, for the X.509
# and CRL entry points (from the gcc call graph, at -O0 = no inlining)
STACK_BUDGET := 32768
stack-check: $(C_OUTPUT_DIR)/ASN1.Pulse.X509.c test/stack.py
	cd $(C_OUTPUT_DIR) && $(CC) -std=c11 -O0 -fcallgraph-info=su -c ASN1.Pulse.X509.c -o stack.o
	python3 test/stack.py --budget $(STACK_BUDGET) $(C_OUTPUT_DIR)/stack.ci \
	  ASN1_Pulse_X509_validate_certificate ASN1_Pulse_X509_validate_crl

.PRECIOUS: $(C_OUTPUT_DIR)/%.c $(C_OUTPUT_DIR)/%.h $(C_OUTPUT_DIR)/test_%.exe $(C_OUTPUT_DIR)/corpus_%.exe $(C_OUTPUT_DIR)/parse_test.exe $(C_OUTPUT_DIR)/write_test.exe $(C_OUTPUT_DIR)/checked_write_test.exe
.PHONY: test test-oracle test-parse test-write test-checked-write test-corpus test-deep-any stack-check FORCE
