PREFIX=Sample.AutoGen_
EVERPARSE_HOME=../..

ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifeq ($(FSTAR_EXE),)
    # fstar.exe not found in PATH, assuming Everest source tree
    FSTAR_HOME=$(realpath $(EVERPARSE_HOME)/../FStar)
  else
    # fstar.exe found in PATH, assuming directory ending with /bin
    FSTAR_HOME=$(realpath $(dir $(FSTAR_EXE))/..)
  endif
  export FSTAR_HOME
endif

LOWPARSE_HOME?=$(EVERPARSE_HOME)/src/lowparse
INCLUDES=$(KRML_HOME)/krmllib \
	$(KRML_HOME)/krmllib/obj \
	$(LOWPARSE_HOME)
INCLUDES_OPTS=$(addprefix --include , $(INCLUDES))
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(INCLUDES_OPTS) $(OTHERFLAGS)

all: verify

.depend: $(PREFIX)color.fst Sample.Client.fst
	$(FSTAR) --dep full $^ > $@

include .depend

verify: $(addsuffix .checked, $(wildcard *.fst *.fsti))

%.checked:
	$(FSTAR) --cache_checked_modules $<

clean:
	rm -f *.checked $(PREFIX)* .depend *~

%.fst-in:
	@echo $(INCLUDES_OPTS)
