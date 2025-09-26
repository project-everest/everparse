
env:
	@echo export FSTAR_EXE=$(FSTAR_EXE)
	@echo export KRML_HOME=$(KRML_HOME)
	@echo export PULSE_HOME=$(PULSE_HOME)
	@if test -d $(EVERPARSE_OPT_PATH)/../_opam ; then opam env ; fi
	@echo export PATH=$(EVERPARSE_OPT_PATH)/FStar/bin:$(EVERPARSE_OPT_PATH)/z3:\"'$$PATH'\"

.PHONY: env
