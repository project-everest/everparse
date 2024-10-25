ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

# Find fstar.exe and the fstar.lib OCaml package
ifeq (,$(FSTAR_HOME))
  _check_fstar := $(shell which fstar.exe)
  ifeq ($(.SHELLSTATUS),0)
    FSTAR_HOME := $(realpath $(dir $(_check_fstar))/..)
  else
#    $(error "FSTAR_HOME is not defined and I cannot find fstar.exe in $(PATH). Please make sure fstar.exe is properly installed and in your PATH or FSTAR_HOME points to its prefix directory or the F* source repository.")
    # assuming Everest layout
    FSTAR_HOME := $(realpath $(EVERPARSE_SRC_PATH)/../../FStar)
  endif
endif
ifeq ($(OS),Windows_NT)
  FSTAR_HOME := $(shell cygpath -m $(FSTAR_HOME))
endif
export FSTAR_HOME
ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
else
    OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
endif
export OCAMLPATH
_check_fstar_lib_package := $(shell env OCAMLPATH="$(OCAMLPATH)" ocamlfind query fstar.lib)
ifneq ($(.SHELLSTATUS),0)
  $(error "Cannot find fstar.lib in $(OCAMLPATH). Please make sure fstar.exe is properly installed and in your PATH or FSTAR_HOME points to its prefix directory or the F* source repository.")
endif
