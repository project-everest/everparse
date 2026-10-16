all: extract-all

EVERPARSE_HOME = $(realpath ../../../../..)

OUTPUT=_output/CDDLTest.Test.fst

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

$(OUTPUT): test.cddl
	$(EVERPARSE_HOME)/bin/everparse-cddl.exe $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(KRML_EXE),--karamel "$(KRML_EXE)") $(if $(Z3_EXE),--z3 "$(Z3_EXE)") $^ --odir $(dir $(OUTPUT)) --fstar_only $(CDDL_ADMIT)

extract-all: $(OUTPUT) $(wildcard *.fst)
	+$(MAKE) -f extract.Makefile test

.PHONY: extract-all all

clean_rules += clean-output

clean-output:
	rm -rf _output

.PHONY: clean-output

# Uncomment if you want to edit the produced F* file
include extract.Makefile
