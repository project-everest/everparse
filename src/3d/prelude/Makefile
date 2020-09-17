all: verify extract

FSTAR_HOME?=$(realpath ../../../../FStar)
KREMLIN_HOME?=$(realpath ../../../../kremlin)
OTHERFLAGS?=
EVERPARSE_HOME=../../..

FSTAR_OPTIONS=$(OTHERFLAGS) $(addprefix --include , $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS) $(OTHERFLAGS) --z3rlimit_factor 8 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100' --cmi

ROOT=$(wildcard *.fst)
ALREADY_CACHED=--already_cached '+Prims +LowStar +FStar +LowParse +C +Spec.Loops'

.depend: $(ROOT)
	$(FSTAR) --dep full $(ROOT) $(ALREADY_CACHED) --extract '* -Prims' > .depend

include .depend

verify: $(ALL_CHECKED_FILES)

extract: EverParse.h

EverParse.rsp: $(ALL_KRML_FILES)
	for f in $^ ; do echo $$f ; done > $@

EverParse.h: EverParse.rsp
	$(KREMLIN_HOME)/krml \
	  -skip-compilation \
	  -bundle 'C.\*,FStar.\*,LowStar.\*[rename=SHOULDNOTBETHERE]' \
	  -bundle 'LowParse.Low.ErrorCode+EverParse3d.InputBuffer.Aux+Prelude.StaticHeader+ResultOps=Prims,LowParse.\*,Prelude,Prelude.\*,Actions,EverParse3d.\*[rename=EverParse,rename-prefix]' \
	  -warn-error -9@4 \
	  -fnoreturn-else -fparentheses -fcurly-braces -fmicrosoft \
	  -header ../noheader.txt \
	  -minimal \
	  -add-include 'EverParse:"EverParseEndianness.h"' \
	  -static-header Prelude.StaticHeader,LowParse.Low.Base,ResultOps,LowParse.Low.ErrorCode,EverParse3d.InputBuffer.Aux \
	  -no-prefix LowParse.Slice \
	  -no-prefix LowParse.Low.BoundedInt \
	  -no-prefix EverParse3d.InputBuffer.Aux \
	  -fextern-c \
	  @$^
	! test -e EverParse.c
	! test -e SHOULDNOTBETHERE.h

%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --extract_module $(basename $(notdir $(subst .checked,,$<)))

%.checked:
	$(FSTAR) $< --cache_checked_modules $(ALREADY_CACHED)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: all verify extract clean

clean:
	rm -f *.checked *.krml EverParse.h EverParse.rsp Makefile.basic Makefile.include .depend
