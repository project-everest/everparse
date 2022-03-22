FSTAR_HOME ?= $(realpath ../../../FStar)
LOWPARSE_HOME ?= $(realpath ../../src/lowparse)
KREMLIN_HOME ?= $(realpath ../../../kremlin)

export FSTAR_HOME
export LOWPARSE_HOME
export KREMLIN_HOME

EXTRACT_TO=ocaml/generated

FSTAR_OPTIONS = --odir $(EXTRACT_TO) --cache_dir cache --cache_checked_modules \
		--already_cached +Prims,+FStar,+LowStar,+C,+Spec.Loops,+LowParse \
		--include $(LOWPARSE_HOME) --include $(KREMLIN_HOME)/kremlib --include $(KREMLIN_HOME)/kremlib/obj --cmi

FSTAR = $(FSTAR_HOME)/bin/fstar.exe --trace_error $(FSTAR_OPTIONS)

FSTAR_FILES=$(wildcard *.fst *.fsti)

all: verify test

cache/%.checked:
	$(FSTAR) $(OTHERFLAGS) $<
	@touch $@

$(EXTRACT_TO)/%.ml:
	$(FSTAR) --codegen OCaml $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

.depend: $(FSTAR_FILES)
	$(FSTAR) --dep full $^ --extract '*,-FStar,-Prims' > .depend.tmp
	mv .depend.tmp $@

depend: .depend

-include .depend

verify: $(ALL_CHECKED_FILES) # from .depend

extract: $(ALL_ML_FILES) # from .depend

test: $(ALL_ML_FILES)
	+$(MAKE) -C ocaml test

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	+$(MAKE) -C ocaml clean
	rm -rf .depend cache out test.exe *~

.PHONY: all depend verify extract clean build test
