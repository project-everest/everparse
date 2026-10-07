EVERPARSE_HOME ?= $(realpath ../../../../../..)
EVERPARSE_SRC_PATH ?= $(EVERPARSE_HOME)/src

LOWPARSE_HOME ?= $(EVERPARSE_SRC_PATH)/lowparse

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
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
		--include $(LOWPARSE_HOME) --include $(LOWPARSE_HOME)/pulse --include $(PULSE_HOME)/lib/pulse --include .. --cmi --ext context_pruning \
		--ext 'optimize_let_vc=false' \
		--warn_error '@272'

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

ifeq ($(OS),Darwin)
KRML_OPTS += -ccopt -Wno-tautological-constant-out-of-range-compare
endif

# -Wno-tautological-overlap-compare because of T32
KRML = $(KRML_EXE) \
	 -fstar $(FSTAR_EXE) \
	 -skip-compilation \
	 -ccopt "-O3" -ccopt "-ffast-math" \
	 -ccopt "-Wno-tautological-overlap-compare" \
	 -drop 'FStar.Tactics.\*' -drop FStar.Tactics -drop 'FStar.Reflection.\*' \
	 -tmpdir out -I .. \
	 -bundle 'FStar.\*,Prims,Pulse.\*,PulseCore.\*,LowParse.\*,C,C.\*' \
	 $(KRML_OPTS) \
	 -warn-error '-2@15-26'
# Warning 2 (unbound reference) is demoted rather than fatal, as in every other
# Pulse build in this repository (e.g. tests/pulse/Makefile). Pulse's extraction
# plugin emits C._zero_for_deref for a reference dereference, but KaRaMeL omits
# its builtin declaration of that symbol whenever Pulse_Lib_Pervasives is among
# the inputs. The reference is harmless: b[C._zero_for_deref] is printed as *b,
# so no such C symbol is ever emitted or needed at link time.
#
# TEMPORARY. This goes away once this branch is merged with fstar2, which is
# based on F* master, whose up-to-date copy of Pulse extracts
# Pulse.Lib.Pervasives._zero_for_deref instead of C._zero_for_deref. That symbol
# does have an implementation among the inputs, so warning 2 will no longer be
# raised and this can be restored to '@2@15-26'.

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

# Link and run, rather than just compiling: ../Test.fst is a real client of the
# generated API, and its main returns non-zero if the validator/jumper/accessor
# chain does not round-trip the field it plants.
test: $(ALL_KRML_FILES) krml/Test.krml
	-@mkdir out
	$(KRML) -no-prefix Test $^
	$(CC) -I out -I .. -o out/test.exe out/*.c
	./out/test.exe

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	-rm -rf cache cache.lax .depend .depend.lax out krml

.PHONY: all depend verify extract clean build test
