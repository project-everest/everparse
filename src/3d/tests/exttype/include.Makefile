ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../../..)
endif
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe

3D=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE)

ifeq (,$(KRML_HOME))
  KRML_HOME := $(realpath ../../../../karamel)
endif
ifeq ($(OS),Windows_NT)
  KRML_HOME := $(shell cygpath -m "$(KRML_HOME)")
endif
export KRML_HOME
