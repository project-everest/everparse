all: verify compile

EVERPARSE_HOME = $(realpath ../..)

LOWPARSE_HOME = $(EVERPARSE_HOME)/lib/everparse/lowparse

INCLUDE_PATHS += $(LOWPARSE_HOME) $(EVERPARSE_HOME)/lib/everparse/asn1/spec

# The library (lib/everparse/asn1/spec) is verified by the toplevel Makefile
# (`make asn1`); only the test modules of this directory are checked here.
ALREADY_CACHED := *,-ASN1.X509,-ASN1.CRL,-ASN1.SetTest,-ASN1.RoundTrip,-ASN1.DiffTest,-ASN1.ExtractionRoot,-ASN1.Spec.Conformance.Examples,

OUTPUT_DIRECTORY := ocaml/extracted

NOT_INCLUDED = ASN1.Tmp.fst ASN1.Test.Interpreter.fst $(wildcard ASN1.bak*)

FSTAR_FILES := $(filter-out $(NOT_INCLUDED),$(wildcard *.fst *.fsti))

clean_rules += ocaml.clean evaluation.clean difftest.clean tool.clean clean-files

# Whole-program extraction.  ASN1.X509, ASN1.CRL, ASN1.SetTest, ASN1.DiffTest
# and ASN1.RoundTrip are what ocaml/ASN1_Parser.ml calls into; everything else
# is reached from them.
CUSTARD_ENTRY_MODULES := ASN1.X509
CUSTARD_ENTRY_MODULES += ASN1.CRL
CUSTARD_ENTRY_MODULES += ASN1.SetTest
CUSTARD_ENTRY_MODULES += ASN1.DiffTest
CUSTARD_ENTRY_MODULES += ASN1.RoundTrip
CUSTARD_ROOTS := ASN1.ExtractionRoot.fst

include $(EVERPARSE_HOME)/lib/everparse/common.Makefile

extract: $(CUSTARD_STAMP)

.PHONY: extract

compile: evaluation/ASN1_Parser.exe

evaluation/ASN1_Parser.exe: $(CUSTARD_STAMP)
	$(MAKE) -C ocaml
	cp ocaml/_build/default/ASN1_Parser.exe evaluation/
	chmod +w $@
	touch $@

test: eval difftest

# Pulse validators extracted to C with Custard (pulse/README.md)
ifeq (,$(NO_PULSE))
test: pulse-test
endif

pulse-test: compile
	+$(MAKE) -C pulse test test-oracle test-corpus test-deep-any stack-check test-parse

eval: compile
	$(MAKE) -C evaluation

# Differential tests against asn1tools, rasn and asn1-rs (difftest/README.md)
difftest: compile
	+$(MAKE) -C difftest

clean-files:
	-rm -rf *.c *.h *.o test.exe krml.rsp *.tmp compile_flags.txt

.PHONY: clean-files

%.clean:
	$(MAKE) -C $(basename $@) clean

.PHONY: %.clean

.PHONY: all compile test eval difftest pulse-test
