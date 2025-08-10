ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

include $(EVERPARSE_SRC_PATH)/windows.Makefile

FSTAR_EXE ?= fstar.exe

FSTAR_VERSION != $(FSTAR_EXE) --version
ifneq ($(.SHELLSTATUS),0)
  $(error "F* version check failed (FSTAR_EXE = $(FSTAR_EXE))" )
endif

export FSTAR_EXE
