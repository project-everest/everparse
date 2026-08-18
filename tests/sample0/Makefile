include Makefile.common

all: verify test

cache/%.checked:
	$(FSTAR) $(OTHERFLAGS) $<
	@touch $@

krml/%.krml:
	$(FSTAR) --codegen krml $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

ifeq (,$(filter clean,$(MAKECMDGOALS)))
-include .depend
endif

.depend: $(QD_FILES) .qd_files
	+$(MAKE) -f Makefile.depend

depend: .depend

verify: $(patsubst %,cache/%.checked,$(QD_FILES))
	echo $*

ALL_KRML_FILES := $(filter-out krml/prims.krml,$(ALL_KRML_FILES))

extract: $(ALL_KRML_FILES) # from .depend
	mkdir -p out
	$(KRML) -warn-error '@2' -skip-compilation $^

test.exe: $(ALL_KRML_FILES)
	mkdir -p out
	$(KRML) $(LOWPARSE_HOME)/LowParse_TestLib_Low_c.c -no-prefix Test $^ -o test.exe

test: test.exe
	./test.exe

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf .depend cache krml out test.exe *~

.PHONY: all depend verify extract clean build test
