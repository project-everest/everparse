all: extract

EVERPARSE_HOME := $(realpath ../../../..)
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m $(EVERPARSE_HOME))
endif

FSTAR_EXE ?= fstar.exe

ifeq (,$(KRML_HOME))
  KRML_HOME := $(realpath ../../../../karamel)
endif
ifeq ($(OS),Windows_NT)
  KRML_HOME := $(shell cygpath -m $(KRML_HOME))
endif
export KRML_HOME

OTHERFLAGS?=

FSTAR_OPTIONS=$(addprefix --include , .. $(EVERPARSE_HOME)/src/lowparse $(KRML_HOME)/krmllib $(KRML_HOME)/krmllib/obj) --z3rlimit_factor 8 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100'
FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --cmi

ROOT=$(wildcard *.fst) $(wildcard *.fsti)
ALREADY_CACHED=--already_cached '*,-EverParse3d.Actions.All,-EverParse3d.InputStream.All,-EverParse3d.InputStream.Extern,-EverParse3d.Actions.BackendFlag,-EverParse3d.Actions.BackendFlagValue'

.depend: $(ROOT)
	$(FSTAR) --dep full $(ROOT) $(ALREADY_CACHED) --extract 'krml:*,-Prims,-FStar.Tactics' --output_deps_to $@

-include .depend

FILTERED_KRML_FILES=$(filter-out ResultOps.krml Actions.krml,$(ALL_KRML_FILES))

extract: extract-extern extract-static

extract-extern: EverParse.h

extract-static: ../static/EverParse.h

EverParse.rsp: $(FILTERED_KRML_FILES) ../EverParse.rsp
	for f in $(FILTERED_KRML_FILES) ; do echo $$f ; done > $@.tmp
	while read file ; do grep "^$$file"'$$' $@.tmp > /dev/null || { echo ../$$file >> $@.tmp ; } ; done < ../EverParse.rsp
	mv $@.tmp $@

KRML_EXTERN = $(KRML_HOME)/krml \
	  -skip-compilation \
	  -skip-makefiles \
	  -bundle 'Prims,C.\*,FStar.\*,LowStar.\*[rename=SHOULDNOTBETHERE]' \
	  -bundle 'EverParse3d.Prelude.StaticHeader+EverParse3d.ErrorCode+EverParse3d.InputStream.Extern.Base+EverParse3d.InputStream.Extern.Type+EverParse3d.CopyBuffer=LowParse.\*,EverParse3d.\*[rename=EverParse,rename-prefix]' \
	  -warn-error -9@4 \
	  -fnoreturn-else -fparentheses -fcurly-braces -fmicrosoft \
	  -header ../../noheader.txt \
	  -minimal \
	  -add-include 'EverParse:"EverParseEndianness.h"' \
	  -static-header 'EverParse3d.Prelude.StaticHeader,LowParse.Low.Base,EverParse3d.ErrorCode,EverParse3d.InputStream.Extern.Type' \
	  -no-prefix LowParse.Slice \
	  -no-prefix LowParse.Low.BoundedInt \
	  -fmicrosoft \
	  -fextern-c

KRML_STATIC = $(KRML_EXTERN) \
	  -tmpdir ../static \
	  -static-header EverParse3d.InputStream.Extern.Base

EverParse.h: EverParse.rsp
	$(KRML_EXTERN) @$^
	test '!' -e EverParse.c
	test '!' -e SHOULDNOTBETHERE.h

../static/EverParse.h: EverParse.rsp
	mkdir -p $(dir $@)
	$(KRML_STATIC) @$^
	test '!' -e $(dir $@)/EverParse.c
	test '!' -e $(dir $@)/SHOULDNOTBETHERE.h

%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml --extract_module $(basename $(notdir $(subst .checked,,$<)))
	touch $@

%.checked:
	$(FSTAR) $< --cache_checked_modules $(ALREADY_CACHED)
	touch $@

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

verify: $(ALL_CHECKED_FILES)

.PHONY: all extract clean verify extract-extern extract-static

clean:
	rm -f *.checked *.krml EverParse.h EverParse.rsp .depend *.tmp .depend.tmp *~ ../static

