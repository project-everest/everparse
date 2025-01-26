ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

FSTAR_EXE ?= fstar.exe

FSTAR_VERSION != $(FSTAR_EXE) --version
ifneq ($(.SHELLSTATUS),0)
  $(error "F* version check failed (FSTAR_EXE = $(FSTAR_EXE))" )
endif

_ != $(FSTAR_EXE) --ocamlenv ocamlfind query fstar.lib
ifneq ($(.SHELLSTATUS),0)
  $(error "Cannot find fstar.lib (FSTAR_EXE = $(FSTAR_EXE)). Is F* properly installed?")
endif

export FSTAR_EXE
