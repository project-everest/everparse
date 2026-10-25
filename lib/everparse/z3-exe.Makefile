ifeq ($(OS),Windows_NT)
ifneq (,$(wildcard $(EVERPARSE_HOME)/opt/z3/z3-$(EVERPARSE_Z3_VERSION).exe))
Z3_EXE ?= $(EVERPARSE_HOME)/opt/z3/z3-$(EVERPARSE_Z3_VERSION).exe
endif
else
ifneq (,$(wildcard $(EVERPARSE_HOME)/opt/z3/z3-$(EVERPARSE_Z3_VERSION)))
Z3_EXE ?= $(EVERPARSE_HOME)/opt/z3/z3-$(EVERPARSE_Z3_VERSION)
endif
endif
