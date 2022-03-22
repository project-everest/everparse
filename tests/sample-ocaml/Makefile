include Makefile.common

all: verify test

cache/%.checked:
	$(FSTAR) $(OTHERFLAGS) $<
	@touch $@

ocaml/%.ml:
	$(FSTAR) --codegen OCaml $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

-include .depend

.depend: $(QD_FILES) .qd_files
	+$(MAKE) -f Makefile.depend

depend: .depend

verify: $(patsubst %,cache/%.checked,$(QD_FILES))
	echo $*

extract: $(ALL_ML_FILES) # from .depend

test: extract
#	./test.exe

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf .depend cache ocaml out test.exe *~

.PHONY: all depend verify extract clean build test
