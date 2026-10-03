all: depend verify test

EVERPARSE_HOME ?= $(realpath ../../../../../..)
EVERPARSE_SRC_PATH ?= $(EVERPARSE_HOME)/src

LOWPARSE_HOME ?= $(EVERPARSE_SRC_PATH)/lowparse

ifdef NO_QD_VERIFY
LAX_EXT=.lax
LAX_OPT=--lax
else
LAX_EXT=
LAX_OPT=
endif

INCLUDE_PATHS += $(LOWPARSE_HOME) $(LOWPARSE_HOME)/pulse ..
ALREADY_CACHED := C,Spec.Loops,LowParse,
CACHE_DIRECTORY := cache$(LAX_EXT)
OUTPUT_DIRECTORY := krml
FSTAR_DEP_FILE := .depend$(LAX_EXT)
FSTAR_FILES := $(wildcard *.fst *.fsti) ../Test.fst

# The point of this test is that every generated module extracts and compiles,
# so each one is a root, not just the part Test.fst happens to exercise.
CUSTARD_BACKEND := KrmlC
CUSTARD_ENTRY_MODULES := Test $(basename $(wildcard *.fst))
CUSTARD_ROOTS := ../Test.fst

clean_rules += clean-local

include $(EVERPARSE_SRC_PATH)/common.Makefile

FSTAR_OPTIONS += $(LAX_OPT) --ext 'optimize_let_vc=false' --warn_error @272

export LOWPARSE_HOME

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
	 -bundle 'FStar.\*,Prims,Pulse.\*,PulseCore.\*,LowParse.\*,C,C.\*,Custard.\*' \
	 $(KRML_OPTS) \
	 -warn-error '@2@15-26'

test: $(CUSTARD_KRML)
	-@mkdir out
	$(KRML) -no-prefix Test $^
	$(CC) -c -I out -I .. $$f out/*.c

depend: $(FSTAR_DEP_FILE)

clean-local:
	-rm -rf out cache cache.lax .depend .depend.lax krml

.PHONY: all depend extract test clean-local
