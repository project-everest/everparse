ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../../../../..)
endif
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile

EVERPARSE_API ?= lowstar
export EVERPARSE_API
3D=$(EVERPARSE_HOME)/bin/everparse-3d.exe --api $(EVERPARSE_API) $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(KRML_EXE),--karamel "$(KRML_EXE)")
