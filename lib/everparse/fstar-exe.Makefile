ifneq (,$(wildcard $(EVERPARSE_HOME)/opt/FStar/out/bin/fstar.exe))
FSTAR_EXE ?= $(EVERPARSE_HOME)/opt/FStar/out/bin/fstar.exe
endif

ifeq ($(OS),Windows_NT)
ifneq (,$(wildcard $(EVERPARSE_HOME)/opt/karamel/out/bin/krml.exe))
KRML_EXE ?= $(EVERPARSE_HOME)/opt/karamel/out/bin/krml.exe
endif
else
ifneq (,$(wildcard $(EVERPARSE_HOME)/opt/karamel/out/bin/krml))
KRML_EXE ?= $(EVERPARSE_HOME)/opt/karamel/out/bin/krml
endif
endif
