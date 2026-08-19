all: verify compile

EVERPARSE_SRC_PATH = $(realpath ..)

LOWPARSE_HOME = $(EVERPARSE_SRC_PATH)/lowparse

INCLUDE_PATHS += $(LOWPARSE_HOME)

ALREADY_CACHED := *,-ASN1Test,-ASN1,

OUTPUT_DIRECTORY := ocaml/extracted

FSTAR_DEP_OPTIONS := --extract '* -Prims -FStar -LowParse.Low -ASN1Test -ASN1.Low'

NOT_INCLUDED = ASN1.Tmp.fst ASN1.Test.Interpreter.fst $(wildcard ASN1.Low.*) ASN1Test.fst $(wildcard ASN1.bak*)

FSTAR_FILES := $(filter-out $(NOT_INCLUDED),$(wildcard *.fst *.fsti))

clean_rules += ocaml.clean evaluation.clean clean-files

include $(EVERPARSE_SRC_PATH)/common.Makefile

FSTAR_OPTIONS += --ext optimize_let_vc

extract: $(ALL_ML_FILES)

.PHONY: extract

krml.rsp: $(ALL_KRML_FILES)
	for f in $^ ; do echo $$f ; done > $@.tmp
	mv $@.tmp $@

Test.c: krml.rsp
	$(KRML_EXE) -fstar $(FSTAR_EXE) \
	  -bundle 'ASN1Test=ASN1Test.\*,Prims,FStar.\*,C.\*,C,LowStar.\*,LowParse.\*' \
	  -no-prefix ASN1Test \
	  -skip-makefiles \
	  -skip-compilation \
	  -o $@ \
	  @$^

compile: evaluation/ASN1_Parser.exe

evaluation/ASN1_Parser.exe: $(ALL_ML_FILES)
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
