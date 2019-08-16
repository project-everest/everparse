include Makefile.common

all: verify test

cache/%.checked:
	$(FSTAR) $(OTHERFLAGS) $<
	@touch $@

kremlin/%.krml:
	$(FSTAR) --codegen Kremlin $(patsubst %.checked,%,$(notdir $<)) --extract_module $(basename $(patsubst %.checked,%,$(notdir $<))) --warn_error '@241'
	@touch $@

.qd_files: $(QD) $(RFC)
	$(QD) $(RFC)
	+$(MAKE) -f Makefile.qd_files

-include .depend

.depend: $(QD_FILES) .qd_files
	+$(MAKE) -f Makefile.depend

depend: .depend

verify: $(patsubst %,cache/%.checked,$(QD_FILES))
	echo $*

ALL_KRML_FILES := $(filter-out kremlin/prims.krml,$(ALL_KRML_FILES))

extract: $(ALL_KRML_FILES) # from .depend
	mkdir -p out
	$(KREMLIN) -warn-error '@2' -skip-compilation $^

test.exe: $(ALL_KRML_FILES)
	mkdir -p out
	$(KREMLIN) $(LOWPARSE_HOME)/LowParse_TestLib_Low_c.c -no-prefix Test $^ -o test.exe

test: test.exe
	./test.exe

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf .qd_files .depend cache kremlin out $(filter-out Test.fst,$(QD_FILES)) test.exe

.PHONY: all depend verify extract clean build test
