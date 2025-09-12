ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

ifeq (,$(PULSE_HOME))
  $(error "PULSE_HOME must point to the root of a pulse installation (probably PULSE_REPO/out)")
endif
PULSE_LIB=$(PULSE_HOME)/lib/pulse

ifeq ($(OS),Windows_NT)
    export PULSE_HOME := $(shell cygpath -m $(PULSE_HOME))
    OCAMLPATH := $(shell cygpath -m $(PULSE_LIB));$(OCAMLPATH)
else
    OCAMLPATH := $(PULSE_LIB):$(OCAMLPATH)
endif
export OCAMLPATH

# Which modules or namespaces are already cached? If all of your
# source files in your project are under the same namespace, say
# MyNamespace, then you can set this variable to *,-MyNamespace
ALREADY_CACHED := PulseCore,Pulse,$(ALREADY_CACHED)

INCLUDE_PATHS += $(PULSE_HOME)/lib/pulse
