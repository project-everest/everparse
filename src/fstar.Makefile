ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

include $(EVERPARSE_SRC_PATH)/windows.Makefile

FSTAR_EXE ?= fstar.exe

export FSTAR_EXE

# Add common options here
FSTAR_OPTIONS += --z3version 4.13.3
