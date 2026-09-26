all: verify compile

EVERPARSE_SRC_PATH = $(realpath ..)

LOWPARSE_HOME = $(EVERPARSE_SRC_PATH)/lowparse

INCLUDE_PATHS += $(LOWPARSE_HOME)

ALREADY_CACHED := *,-ASN1Test,-ASN1,

OUTPUT_DIRECTORY := ocaml/extracted

NOT_INCLUDED = ASN1.Tmp.fst ASN1.Test.Interpreter.fst $(wildcard ASN1.Low.*) ASN1Test.fst $(wildcard ASN1.bak*)

FSTAR_FILES := $(filter-out $(NOT_INCLUDED),$(wildcard *.fst *.fsti))

clean_rules += ocaml.clean evaluation.clean clean-files

# Whole-program extraction.  ASN1.X509 and ASN1.CRL are what ocaml/ASN1_Parser.ml
# calls into; everything else is reached from them.
CUSTARD_ENTRY_MODULES := ASN1.X509
CUSTARD_ENTRY_MODULES += ASN1.CRL
CUSTARD_ROOTS := ASN1.CRL.fst

include $(EVERPARSE_SRC_PATH)/common.Makefile

FSTAR_OPTIONS += --ext optimize_let_vc

extract: $(CUSTARD_STAMP)

.PHONY: extract

compile: evaluation/ASN1_Parser.exe

evaluation/ASN1_Parser.exe: $(CUSTARD_STAMP)
	$(MAKE) -C ocaml
	cp ocaml/_build/default/ASN1_Parser.exe evaluation/
	chmod +w $@
	touch $@

test: eval

eval: compile
	$(MAKE) -C evaluation

clean-files:
	-rm -rf *.c *.h *.o test.exe krml.rsp *.tmp compile_flags.txt

.PHONY: clean-files

%.clean:
	$(MAKE) -C $(basename $@) clean

.PHONY: %.clean

.PHONY: all compile test eval
