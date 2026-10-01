ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../../..)
endif
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

FSTAR_EXE ?= fstar.exe

3D=$(EVERPARSE_HOME)/bin/3d.exe --fstar $(FSTAR_EXE) --pulse
