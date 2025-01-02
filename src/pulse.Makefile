ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

ifeq (,$(PULSE_LIB))
  ifeq (,$(PULSE_HOME))
    PULSE_LIB := $(shell ocamlfind query pulse)
    ifeq (,$(PULSE_LIB))
#      $(error "Pulse should be installed and its lib/ subdirectory should be in ocamlpath; or PULSE_HOME should be defined in the enclosing Makefile as the prefix directory where Pulse was installed, or the root directory of its source repository")
      # assuming Everest layout
      # NOTE: $PULSE_HOME is now $PULSE_REPO/out, cf. FStarLang/pulse#246
      PULSE_LIB := $(realpath $(EVERPARSE_SRC_PATH)/../../pulse/out/lib/pulse)
    endif
    PULSE_HOME := $(realpath $(PULSE_LIB)/../..)
  else
    PULSE_LIB := $(PULSE_HOME)/lib/pulse
  endif
endif
ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(PULSE_LIB);$(OCAMLPATH)
else
    OCAMLPATH := $(PULSE_LIB):$(OCAMLPATH)
endif
export OCAMLPATH

# Which modules or namespaces are already cached? If all of your
# source files in your project are under the same namespace, say
# MyNamespace, then you can set this variable to *,-MyNamespace
ALREADY_CACHED := PulseCore,Pulse,$(ALREADY_CACHED)

# FIXME: do we still need separate subdirectories for pledges, classes?
INCLUDE_PATHS += $(PULSE_LIB) $(PULSE_LIB)/lib $(PULSE_LIB)/lib/class $(PULSE_LIB)/lib/pledge $(PULSE_LIB)/core

FSTAR_OPTIONS += --load_cmxs pulse
