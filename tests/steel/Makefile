all: depend verify test

FSTAR_HOME ?= ../../../FStar
LOWPARSE_HOME ?= ../../src/lowparse
KRML_HOME ?= ../../../karamel

export FSTAR_HOME
export LOWPARSE_HOME
export KRML_HOME

DEPEND_FILE=.depend
CACHE_DIR=cache
CHECKED_EXT=.checked

FSTAR_OPTIONS := --odir krml --cache_dir $(CACHE_DIR) $(LAX_OPT) --cache_checked_modules \
		--already_cached '*,-Test' \
		--include $(FSTAR_HOME)/ulib/.cache \
		--include $(FSTAR_HOME)/ulib \
		--include $(FSTAR_HOME)/ulib/experimental \
		--include $(LOWPARSE_HOME) \
		--include $(KRML_HOME)/krmllib --include $(KRML_HOME)/krmllib/obj --cmi

ifdef STEEL_C
FSTAR_EXE=$(FSTAR_HOME)/examples/steel/arraystructs/my_fstar/bin/fstar.exe
FSTAR_LIB=$(FSTAR_HOME)/ulib
export FSTAR_LIB
FSTAR_OPTIONS += --include $(LOWPARSE_HOME)/steel_c_array

$(FSTAR_EXE):
	+$(MAKE) -C $(FSTAR_HOME)/examples/steel/arraystructs/my_fstar

else
FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
FSTAR_OPTIONS += --include $(LOWPARSE_HOME)/steel_array
endif

FSTAR = $(FSTAR_EXE) --trace_error $(FSTAR_OPTIONS)

HEADERS = $(addprefix -add-include ,'"krml/internal/compat.h"')

KRML = $(KRML_HOME)/krml \
	 -ccopt "-Ofast" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out \
	 -bundle 'Test=Steel.\*,C,LowStar.\*,LowParse.\*' \
	 $(HEADERS) \
	 -warn-error '@2'

QD_FILES = $(wildcard *.fst *.fsti)

$(CACHE_DIR)/%$(CHECKED_EXT):
	$(FSTAR) $(OTHERFLAGS) $<
	@touch $@

krml/%.krml:
	$(FSTAR) --codegen krml $(patsubst %$(CHECKED_EXT),%,$(notdir $<)) --extract_module $(basename $(patsubst %$(CHECKED_EXT),%,$(notdir $<))) --warn_error '@241'
	@touch $@

$(DEPEND_FILE): $(QD_FILES) Makefile $(FSTAR_EXE)
	$(FSTAR) --dep full --extract '*,-Steel,+Steel.Loops,+Steel.ST.HigherArray,-FStar.NMST,-FStar.NMSTTotal,-FStar.MST,-FStar.MSTTotal,-LowParse.SteelST.Fold,-FStar.Monotonic.Heap' $(QD_FILES) Test.fst > $@.tmp
	mv $@.tmp $@

depend: $(DEPEND_FILE)

-include $(DEPEND_FILE)

verify: $(patsubst %,$(CACHE_DIR)/%$(CHECKED_EXT),$(QD_FILES))
	echo $*

ALL_KRML_FILES := $(filter-out krml/prims.krml,$(ALL_KRML_FILES))

test.exe: $(ALL_KRML_FILES) main.c
	-@mkdir out
	$(KRML) -no-prefix Test $^ -o test.exe

extract: test.exe

test: test.exe input.dat
	./test.exe
	diff input.dat output.dat

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	-rm -rf cache cache.lax .depend .depend.tmp .depend.lax out krml test.exe

.PHONY: all depend verify extract clean build test
