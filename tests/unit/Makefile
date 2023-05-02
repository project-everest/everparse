ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifeq ($(FSTAR_EXE),)
    # fstar.exe not found in PATH, assuming Everest source tree
    FSTAR_HOME=$(realpath ../../../FStar)
  else
    # fstar.exe found in PATH, assuming directory ending with /bin
    FSTAR_HOME=$(realpath $(dir $(FSTAR_EXE))/..)
  endif
  export FSTAR_HOME
endif

LOWPARSE_HOME ?= ../../src/lowparse
KRML_HOME ?= ../../../karamel

export FSTAR_HOME
export LOWPARSE_HOME
export KRML_HOME

ifdef NO_QD_VERIFY
LAX_EXT=.lax
LAX_OPT=--lax
else
LAX_EXT=
LAX_OPT=
endif

DEPEND_FILE=.depend$(LAX_EXT)
CACHE_DIR=cache$(LAX_EXT)
CHECKED_EXT=.checked$(LAX_EXT)

FSTAR_OPTIONS = --odir krml --cache_dir $(CACHE_DIR) $(LAX_OPT) --cache_checked_modules \
		--already_cached +Prims,+FStar,+LowStar,+C,+Spec.Loops,+LowParse \
		--include $(LOWPARSE_HOME) --include $(KRML_HOME)/krmllib --include $(KRML_HOME)/krmllib/obj --include .. --cmi

FSTAR = $(FSTAR_HOME)/bin/fstar.exe --trace_error $(FSTAR_OPTIONS)

HEADERS = $(addprefix -add-include ,'"krml/internal/compat.h"')

KRML = $(KRML_HOME)/krml \
	 -ccopt "-Ofast" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out -I .. \
	 -bundle 'LowParse.\*' \
	 $(HEADERS) \
	 -warn-error '@2'

QD_FILES = $(wildcard *.fst *.fsti)

all: depend verify test

# Don't re-verify standard library
$(CACHE_DIR)/FStar.%$(CHECKED_EXT) \
$(CACHE_DIR)/LowStar.%$(CHECKED_EXT) \
$(CACHE_DIR)/C.%$(CHECKED_EXT) \
$(CACHE_DIR)/LowParse.%$(CHECKED_EXT):
	$(FSTAR) --admit_smt_queries true $<
	@touch $@

$(CACHE_DIR)/%$(CHECKED_EXT):
	$(FSTAR) $(OTHERFLAGS) $<
	@touch $@

krml/%.krml:
	$(FSTAR) --codegen krml $(patsubst %$(CHECKED_EXT),%,$(notdir $<)) --extract_module $(basename $(patsubst %$(CHECKED_EXT),%,$(notdir $<))) --warn_error '@241'
	@touch $@

$(DEPEND_FILE): $(QD_FILES) Makefile ../Test.fst
	$(FSTAR) --dep full $(QD_FILES) Test.fst > $@

depend: $(DEPEND_FILE)

-include $(DEPEND_FILE)

ifdef NO_QD_VERIFY
verify:
else
verify: $(patsubst %,$(CACHE_DIR)/%$(CHECKED_EXT),$(QD_FILES))
	echo $*
endif

ALL_KRML_FILES := $(filter-out krml/prims.krml,$(ALL_KRML_FILES))

extract: $(ALL_KRML_FILES) # from .depend
	-@mkdir out
	$(KRML) -skip-compilation $^

test.exe: $(ALL_KRML_FILES) krml/Test.krml
	-@mkdir out
	$(KRML) $(LOWPARSE_HOME)/LowParse_TestLib_Low_c.c -no-prefix Test $^ -o test.exe

test: test.exe
	./test.exe

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	-rm -rf cache cache.lax .depend .depend.lax out

.PHONY: all depend verify extract clean build test
