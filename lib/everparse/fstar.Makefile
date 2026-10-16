ifeq (,$(EVERPARSE_HOME))
  $(error "EVERPARSE_HOME must be set to the absolute path of the root of the EverParse repository or installation")
endif

include $(EVERPARSE_HOME)/lib/everparse/windows.Makefile

-include $(EVERPARSE_HOME)/lib/everparse/fstar-exe.Makefile
FSTAR_EXE ?= fstar.exe
KRML_EXE ?= krml.exe

export FSTAR_EXE

include $(EVERPARSE_HOME)/lib/everparse/z3-version.Makefile
ifneq (,$(Z3_EXE))
FSTAR_OPTIONS += --smt $(Z3_EXE)
endif
ifneq (,$(EVERPARSE_Z3_VERSION))
FSTAR_OPTIONS += --z3version $(EVERPARSE_Z3_VERSION)
endif
