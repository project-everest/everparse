
export FSTAR_EXE  := $(EVERPARSE_OPT_PATH)/FStar/bin/fstar.exe
export KRML_HOME  := $(EVERPARSE_OPT_PATH)/karamel
export PULSE_HOME := $(EVERPARSE_OPT_PATH)/pulse/out
export HACL_HOME := $(EVERPARSE_OPT_PATH)/hacl-star
export PATH := $(EVERPARSE_OPT_PATH)/z3:$(PATH)

env:
	@echo export FSTAR_EXE=$(FSTAR_EXE)
	@echo export KRML_HOME=$(KRML_HOME)
	@echo export PULSE_HOME=$(PULSE_HOME)
	@echo export HACL_HOME=$(HACL_HOME)
	@echo export PATH=$(EVERPARSE_OPT_PATH)/FStar/bin:$(EVERPARSE_OPT_PATH)/z3:\"'$$PATH'\"

.PHONY: env
