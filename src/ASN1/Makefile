all: verify test

ifndef KREMLIN_HOME
    $(error Please clone https://github.com/FStarLang/kremlin and point KREMLIN_HOME to that clone)
endif

ifndef EVERPARSE_HOME
  $(error Please clone https://github.com/project-everest/everparse and point EVERPARSE_HOME to that clone)
endif

LOWPARSE_HOME=$(EVERPARSE_HOME)/src/lowparse

INCLUDE_PATH = $(LOWPARSE_HOME) $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj

OTHERFLAGS = --admit_smt_queries true

FSTAR_OPTIONS = --cache_checked_modules \
		--already_cached *,-ASN1Test,-ASN1 \
		$(SKIP_VERIFICATION) \
		--cmi \
		$(addprefix --include ,$(INCLUDE_PATH)) \
		$(OTHERFLAGS)

ifdef FSTAR_HOME
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe
else
FSTAR_EXE = fstar.exe
endif
FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

ALL_SOURCE_FILES = $(wildcard *.fst *.fsti)

.depend: $(ALL_SOURCE_FILES) Makefile
	$(FSTAR) --dep full $(ALL_SOURCE_FILES) > $@.tmp
	mv $@.tmp $@

depend: .depend

-include .depend

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR) $<
	@touch -c $@

verify: $(ALL_CHECKED_FILES)
	echo $*

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

%.krml:
	$(FSTAR) --codegen Kremlin $(notdir $(basename $<)) --extract_module $(notdir $(basename $(basename $<))) --warn_error '@241'
	touch $@

kremlin.rsp: $(ALL_KRML_FILES)
	for f in $^ ; do echo $$f ; done > $@.tmp
	mv $@.tmp $@

Test.c: kremlin.rsp
	$(KREMLIN_HOME)/krml \
	  -bundle 'ASN1Test=ASN1Test.\*,Prims,FStar.\*,C.\*,C,LowStar.\*,LowParse.\*' \
	  -no-prefix ASN1Test \
	  -skip-makefiles \
	  -skip-compilation \
	  -o $@ \
	  @$^

test: ASN1Test.c # test.exe
	cat $^

clean:
	-rm -rf *.checked *.krml .depend out *.c *.h *.o test.exe kremlin.rsp *.tmp compile_flags.txt

.PHONY: all verify clean depend test
