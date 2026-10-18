ifeq ($(OS),Windows_NT)
ifneq (,$(wildcard $(EVERPARSE_HOME)/lib/fstar/z3-$(EVERPARSE_Z3_VERSION)/bin/z3.exe))
Z3_EXE ?= $(EVERPARSE_HOME)/lib/fstar/z3-$(EVERPARSE_Z3_VERSION)/bin/z3.exe
endif
else
ifneq (,$(wildcard $(EVERPARSE_HOME)/lib/fstar/z3-$(EVERPARSE_Z3_VERSION)/bin/z3))
Z3_EXE ?= $(EVERPARSE_HOME)/lib/fstar/z3-$(EVERPARSE_Z3_VERSION)/bin/z3
endif
endif
