EVERPARSE_HOME ?= $(realpath ../../../../../..)
EVERPARSE_SRC_PATH ?= $(EVERPARSE_HOME)/src

LOWPARSE_HOME ?= $(EVERPARSE_SRC_PATH)/lowparse

include $(EVERPARSE_SRC_PATH)/fstar.Makefile

export FSTAR_EXE
export LOWPARSE_HOME

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

FSTAR_OPTIONS += --odir krml --cache_dir $(CACHE_DIR) $(LAX_OPT) --cache_checked_modules \
		--already_cached +Prims,+FStar,+LowStar,+C,+Spec.Loops,+LowParse \
		--include $(LOWPARSE_HOME) --include $(LOWPARSE_HOME)/pulse --include .. --ext context_pruning \
		--ext 'optimize_let_vc=false' \
		--warn_error '@272'

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

HEADERS = $(addprefix -add-include ,'"krml/internal/compat.h"')

# -Wno-tautological-overlap-compare because of T32
KRML = $(KRML_EXE) \
	 -fstar $(FSTAR_EXE) \
	 -ccopt "-O3" -ccopt "-ffast-math" \
	 -ccopt "-Wno-tautological-overlap-compare" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out -I .. \
	 -bundle 'LowParse.\*' \
	 $(KRML_OPTS) \
	 $(HEADERS) \
	 -warn-error '@2-26'

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

$(DEPEND_FILE): $(QD_FILES) Makefile
	$(FSTAR) --dep full $(QD_FILES) ../Test.fst --output_deps_to $@ --extract '*,-FStar.Tactics,-FStar.Reflection,-Pulse,+Pulse.Lib.Pervasives,+Pulse.Lib.Slice'

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
	-rm -rf cache cache.lax .depend .depend.lax out krml

.PHONY: all depend verify extract clean build test
