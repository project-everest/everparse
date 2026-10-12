# Auxiliary Makefile invoked recursively from the parent roundtrip
# Makefile, once per target instance, to run F* (typecheck + OCaml
# extraction) via the standard EverParse common.Makefile.
#
# Required variables (must be passed on the command line by the
# parent):
#   MNAME            -- F* module name (e.g. RoundtripDpe).
#   OUTPUT_DIRECTORY -- directory containing $(MNAME).fst (e.g.
#                       _output/dpe); $(MNAME).fst.checked and
#                       $(MNAME).ml are produced there too.
#
# The .fst file must already exist when this Makefile is invoked: the
# parent is responsible for generating it via gen_fst.exe.

all: extract

ifeq (,$(MNAME))
$(error MNAME must be set on the command line)
endif
ifeq (,$(OUTPUT_DIRECTORY))
$(error OUTPUT_DIRECTORY must be set on the command line)
endif

EVERPARSE_HOME := $(realpath ../../../..)

# karamel.Makefile adds krmllib paths; pulse.Makefile adds
# PULSE_HOME/lib/pulse and sets OCAMLPATH for pulse extraction.
INCLUDE_PATHS += \
    $(EVERPARSE_HOME)/src/cbor/spec \
    $(EVERPARSE_HOME)/src/cbor/pulse \
    $(EVERPARSE_HOME)/src/cddl/spec \
    $(EVERPARSE_HOME)/src/cddl/pulse \
    $(EVERPARSE_HOME)/src/cddl/tool

ALREADY_CACHED := *,-$(MNAME),

# Whole-program extraction of just this module: the checker links the result
# against evercddl.lib, which already holds the CDDL AST, so $(MNAME) alone is
# the public surface.
CUSTARD_BACKEND := OCaml
CUSTARD_ENTRY_MODULES := $(MNAME)
FSTAR_FILES := $(OUTPUT_DIRECTORY)/$(MNAME).fst
CACHE_DIRECTORY := $(OUTPUT_DIRECTORY)
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

include $(EVERPARSE_HOME)/src/karamel.Makefile
include $(EVERPARSE_HOME)/src/pulse.Makefile
include $(EVERPARSE_HOME)/src/common.Makefile

extract: $(CUSTARD_STAMP)

.PHONY: all extract
