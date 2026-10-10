ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

include $(EVERPARSE_SRC_PATH)/windows.Makefile

FSTAR_EXE ?= fstar.exe

export FSTAR_EXE

include $(EVERPARSE_SRC_PATH)/z3-version.Makefile
FSTAR_OPTIONS += --z3version $(EVERPARSE_Z3_VERSION)
