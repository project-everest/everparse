include Makefile.common

all: verify test

cache/%.checked:
	$(FSTAR) $(OTHERFLAGS) $<
	@touch $@

krml/%.krml:
	$(FSTAR) --codegen krml $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

-include .depend

.qd_files: $(QD_FILES)
	+$(MAKE) -f Makefile.qd_files

ifeq (,$(filter clean,$(MAKECMDGOALS)))
.depend: .qd_files
	+$(MAKE) -f Makefile.depend
endif

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
	rm -rf .qd_files .depend cache krml out $(filter-out Test.fst,$(QD_FILES)) test.exe

.PHONY: all depend verify extract clean build test
