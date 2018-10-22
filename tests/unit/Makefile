FSTAR_HOME ?= ../../../FStar
MITLS_HOME ?= ../../../mitls-fstar
KREMLIN_HOME ?= ../../../kremlin

export FSTAR_HOME
export MITLS_HOME
export KREMLIN_HOME

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

HINTS_OPTS=--hint_file hints/$(notdir $(subst .checked,,$<)).hints
FSTAR_OPTIONS = --odir kremlin --cache_dir $(CACHE_DIR) $(LAX_OPT) --cache_checked_modules --use_hints \
		--include $(MITLS_HOME)/src/lowparse --include $(KREMLIN_HOME)/kremlib

FSTAR = $(FSTAR_HOME)/bin/fstar.exe --trace_error $(FSTAR_OPTIONS)

HEADERS = $(addprefix -add-include ,'"hacks.h"' \
  '"kremlin/prims_string.h"' '"kremlin/prims_int.h"' '"kremlin/c_string.h"')

KREMLIN = $(KREMLIN_HOME)/krml \
	 -ccopt "-Ofast" \
	 -drop FStar.Bytes -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out -I .. \
	 -bundle 'LowParse.\*' \
	 $(HEADERS) \
	 -warn-error -9

QD_FILES = $(wildcard *.fst *.fsti)

$(CACHE_DIR)/%$(CHECKED_EXT):
	$(FSTAR) $(HINTS_OPTS) --record_hints $<
	@touch $@

kremlin/%.krml:
	$(FSTAR) --codegen Kremlin $(patsubst %$(CHECKED_EXT),%,$(notdir $<)) --extract_module $(basename $(patsubst %$(CHECKED_EXT),%,$(notdir $<))) --warn_error '@241'
	@touch $@

$(DEPEND_FILE): $(QD_FILES) Makefile hints
	$(FSTAR) --dep full $(QD_FILES) > $@

all: $(DEPEND_FILE) verify extract

hints:
	mkdir hints

-include $(DEPEND_FILE)

ifdef NO_QD_VERIFY
verify:
else
verify: $(patsubst %,$(CACHE_DIR)/%$(CHECKED_EXT),$(QD_FILES))
	echo $*
endif

ALL_KRML_FILES := $(filter-out kremlin/prims.krml,$(ALL_KRML_FILES))

extract: $(ALL_KRML_FILES) # from .depend
	-@mkdir out
	$(KREMLIN) -skip-compilation $^

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS) --hint_file hints/$(notdir $(subst -in,.hints,$@))

clean:
	-rm -rf cache cache.lax .depend .depend.lax out

.PHONY: all verify extract clean build
