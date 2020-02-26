3D=../3d

ALREADY_CACHED=--already_cached '+Prims +LowStar +FStar +LowParse +C +Prelude +Actions +ResultOps +C.Loops +Spec' --cache_dir out
EVERPARSE_HOME?=../../..
FSTAR_HOME?=$(EVERPARSE_HOME)/../FStar
KREMLIN_HOME?=$(EVERPARSE_HOME)/../kremlin
OTHERFLAGS?=
INCLUDES=out $(EVERPARSE_HOME)/src/3d/prelude $(EVERPARSE_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib
ROOT=out/TestActions1.fst
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(addprefix --include , $(INCLUDES)) --odir out $(OTHERFLAGS) $(ALREADY_CACHED) --z3rlimit_factor 8 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2 --z3cliopt 'smt.qi.eager_threshold=100' --cmi
KREMLIN = $(KREMLIN_HOME)/krml \
	 -ccopt "-Ofast" \
	 -tmpdir out \
	 -bundle 'ResultOps=Prims,C.*,FStar.*,LowStar.*,LowParse.*,Prelude,Prelude.*,EverParse3d.*,Actions[rename=EverParse,rename-prefix]' \
	 $(HEADERS) \
	 $(KRML_FLAGS) \
	 -warn-error -9 \
	 -fnoreturn-else \
	 -fparentheses \
	 -fcurly-braces \
	 -fmicrosoft \
	 -header noheader.txt \
	 -minimal \
	 -I .. \
	 -add-include 'EverParse:"EverParseEndianness.h"' \
	 -add-include '<stdbool.h>' \
	 -add-include '<stdint.h>' \
	 -static-header Prelude.StaticHeader,LowParse.Low.Base,Prelude,Actions,ResultOps \
	 -no-prefix LowParse.Slice \
	 -no-prefix LowParse.Low.BoundedInt

all: $(ROOT)
	+$(MAKE) codegen

test:
	+$(MAKE) -B $(ROOT)
	+$(MAKE) all

out/%.fst: %.3d
	mkdir -p out
	$(3D) --module_name $* $^
	$(FSTAR) --print_in_place $@  #implementation
	$(FSTAR) --print_in_place $@i #interface

# JP: incorrect regeneration of .depend, non-standard name for the dependency
# file
.dep: $(ROOT)
	$(FSTAR) --dep full $(ROOT) --extract '* -Prims' > .dep

include .dep

codegen: $(ALL_KRML_FILES)
	$(KREMLIN) -skip-linking $^ $(subst .fst,,$(ROOT))Wrapper.c
	clang-format -i --style=Microsoft $(subst .fst,,$(ROOT)).c $(subst .fst,,$(ROOT)).h $(subst .fst,,$(ROOT))Wrapper.c $(subst .fst,,$(ROOT))Wrapper.h || true

kremlin: $(ALL_KRML_FILES)

#$(ROOT).checked:  OTHERFLAGS+=--admit_smt_queries true
out/%.checked:
	$(FSTAR) $< --cache_checked_modules

out/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin --extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: all codegen kremlin test

out/%.c: out/%.fst
