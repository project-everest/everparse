ifneq (,$(wildcard $(EVERPARSE_HOME)/bin/fstar.exe))
FSTAR_EXE ?= $(EVERPARSE_HOME)/bin/fstar.exe
endif

ifeq ($(OS),Windows_NT)
ifneq (,$(wildcard $(EVERPARSE_HOME)/bin/krml.exe))
KRML_EXE ?= $(EVERPARSE_HOME)/bin/krml.exe
endif
else
ifneq (,$(wildcard $(EVERPARSE_HOME)/bin/krml))
KRML_EXE ?= $(EVERPARSE_HOME)/bin/krml
endif
endif
