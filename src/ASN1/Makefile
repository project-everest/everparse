all: verify compile

EVERPARSE_HOME ?= ../..
KRML_HOME ?= $(EVERPARSE_HOME)/../karamel

LOWPARSE_HOME=$(EVERPARSE_HOME)/src/lowparse

INCLUDE_PATH = $(LOWPARSE_HOME) $(KRML_HOME)/krmllib $(KRML_HOME)/krmllib/obj

FSTAR_OPTIONS = --cache_checked_modules --ext optimize_let_vc \
		--already_cached *,-ASN1Test,-ASN1 \
		--cmi \
	        --odir ocaml/extracted \
		$(addprefix --include ,$(INCLUDE_PATH)) \
		$(OTHERFLAGS)


FSTAR_EXE ?= fstar.exe

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

NOT_INCLUDED=ASN1.Tmp.fst ASN1.Test.Interpreter.fst $(wildcard ASN1.Low.*) ASN1Test.fst $(wildcard ASN1.bak*)

ALL_SOURCE_FILES = $(filter-out $(NOT_INCLUDED), $(wildcard *.fst *.fsti))

.depend: $(ALL_SOURCE_FILES) Makefile
	$(FSTAR) --dep full --extract '* -Prims -FStar -LowParse.Low -ASN1Test -ASN1.Low' $(ALL_SOURCE_FILES) --output_deps_to $@

depend: .depend

ifeq (,$(filter clean,$(MAKECMDGOALS)))
-include .depend
endif

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR) $<
	@touch -c $@

verify: $(ALL_CHECKED_FILES)
	echo $*

extract: $(ALL_ML_FILES)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

ocaml/extracted/%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<)))

ocaml/%.krml:
	$(FSTAR) --codegen krml $(notdir $(basename $<)) --extract_module $(notdir $(basename $(basename $<))) --warn_error '@241'
	touch $@

krml.rsp: $(ALL_KRML_FILES)
	for f in $^ ; do echo $$f ; done > $@.tmp
	mv $@.tmp $@

Test.c: krml.rsp
	$(KRML_HOME)/krml -fstar $(FSTAR_EXE) \
	  -bundle 'ASN1Test=ASN1Test.\*,Prims,FStar.\*,C.\*,C,LowStar.\*,LowParse.\*' \
	  -no-prefix ASN1Test \
	  -skip-makefiles \
	  -skip-compilation \
	  -o $@ \
	  @$^

# test: ASN1Test.c # test.exe
#	cat $^

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
	-rm -rf *.checked *.krml .depend *.c *.h *.o test.exe krml.rsp *.tmp compile_flags.txt

.PHONY: clean-files

%.clean:
	$(MAKE) -C $(basename $@) clean

.PHONY: %.clean

clean: ocaml.clean evaluation.clean clean-files

.PHONY: all verify clean depend compile test eval
