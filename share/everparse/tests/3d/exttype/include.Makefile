ifeq (,$(EVERPARSE_HOME))
  EVERPARSE_HOME := $(realpath ../../../../..)
endif
ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m "$(EVERPARSE_HOME)")
endif
export EVERPARSE_HOME

include $(EVERPARSE_HOME)/lib/everparse/fstar.Makefile

3D=$(EVERPARSE_HOME)/bin/everparse-3d.exe $(if $(FSTAR_EXE),--fstar "$(FSTAR_EXE)") $(if $(Z3_EXE),--z3_executable "$(Z3_EXE)") --api pulse
