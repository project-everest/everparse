ifeq (,$(EVERPARSE_HOME))
  $(error "EVERPARSE_HOME must be set to the absolute path of the root of the EverParse repository or installation")
endif

include $(EVERPARSE_HOME)/src/windows.Makefile

FSTAR_EXE ?= fstar.exe

export FSTAR_EXE

include $(EVERPARSE_HOME)/src/z3-version.Makefile
FSTAR_OPTIONS += --z3version $(EVERPARSE_Z3_VERSION)
