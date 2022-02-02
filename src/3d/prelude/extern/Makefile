all: extract

FSTAR_HOME?=$(realpath ../../../../../FStar)
KREMLIN_HOME?=$(realpath ../../../../../kremlin)
OTHERFLAGS?=
EVERPARSE_HOME=../../../..

FSTAR_OPTIONS=$(addprefix --include , .. $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/obj) --z3rlimit_factor 8 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100'
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS) $(OTHERFLAGS) --cmi

ROOT=$(wildcard *.fst) $(wildcard *.fsti)
ALREADY_CACHED=--already_cached '*,-EverParse3d.Actions.All,-EverParse3d.InputStream.All,-EverParse3d.InputStream.Extern,-EverParse3d.Actions.BackendFlag,-EverParse3d.Actions.BackendFlagValue'

.depend: $(ROOT)
	$(FSTAR) --dep full $(ROOT) $(ALREADY_CACHED) --extract '* -Prims' > $@.tmp
	mv $@.tmp $@

-include .depend

FILTERED_KRML_FILES=$(filter-out ResultOps.krml Actions.krml,$(ALL_KRML_FILES))

extract: EverParse.h

EverParse.rsp: $(FILTERED_KRML_FILES) ../EverParse.rsp
	for f in $(FILTERED_KRML_FILES) ; do echo $$f ; done > $@.tmp
	while read file ; do grep "^$$file"'$$' $@.tmp > /dev/null || { echo ../$$file >> $@.tmp ; } ; done < ../EverParse.rsp
	mv $@.tmp $@

EverParse.h: EverParse.rsp
	$(KREMLIN_HOME)/krml \
	  -skip-compilation \
	  -skip-makefiles \
	  -bundle 'Prims,C.\*,FStar.\*,LowStar.\*[rename=SHOULDNOTBETHERE]' \
	  -bundle 'EverParse3d.Prelude.StaticHeader+EverParse3d.ErrorCode+EverParse3d.InputStream.Extern.Base+EverParse3d.InputStream.Extern.Type=LowParse.\*,EverParse3d.\*[rename=EverParse,rename-prefix]' \
	  -warn-error -9@4 \
	  -fnoreturn-else -fparentheses -fcurly-braces -fmicrosoft \
	  -header ../../noheader.txt \
	  -minimal \
	  -add-include 'EverParse:"EverParseEndianness.h"' \
	  -static-header 'EverParse3d.Prelude.StaticHeader,LowParse.Low.Base,EverParse3d.ErrorCode,EverParse3d.InputStream.Extern.Type' \
	  -no-prefix LowParse.Slice \
	  -no-prefix LowParse.Low.BoundedInt \
	  -fextern-c \
	  @$^
	test '!' -e EverParse.c
	test '!' -e SHOULDNOTBETHERE.h

%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --extract_module $(basename $(notdir $(subst .checked,,$<)))
	touch $@

%.checked:
	$(FSTAR) $< --cache_checked_modules $(ALREADY_CACHED)
	touch $@

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

verify: $(ALL_CHECKED_FILES)

.PHONY: all extract clean verify

clean:
	rm -f *.checked *.krml EverParse.h EverParse.rsp .depend *.tmp .depend.tmp *~

