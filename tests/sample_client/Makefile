PREFIX=Sample.AutoGen_
EVERPARSE_HOME=../..

include $(EVERPARSE_HOME)/src/karamel.Makefile

FSTAR_EXE ?= fstar.exe
LOWPARSE_HOME?=$(EVERPARSE_HOME)/src/lowparse

INCLUDES=$(LOWPARSE_HOME)
INCLUDES_OPTS=$(addprefix --include , $(INCLUDES))
FSTAR=$(FSTAR_EXE) $(FSTAR_OPTIONS) $(INCLUDES_OPTS) $(OTHERFLAGS)

all: verify

.depend: $(PREFIX)color.fst Sample.Client.fst
	$(FSTAR) --dep full $^ --output_deps_to $@

include .depend

verify: $(addsuffix .checked, $(wildcard *.fst *.fsti))

%.checked:
	$(FSTAR) --cache_checked_modules $<

clean:
	rm -f *.checked $(PREFIX)* .depend *~

%.fst-in:
	@echo $(INCLUDES_OPTS)
