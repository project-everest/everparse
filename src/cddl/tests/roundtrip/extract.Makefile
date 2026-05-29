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

EVERPARSE_SRC_PATH := $(realpath ../../..)

# karamel.Makefile adds KRML_HOME/krmllib paths; pulse.Makefile adds
# PULSE_HOME/lib/pulse and sets OCAMLPATH for pulse extraction.
INCLUDE_PATHS += \
    $(EVERPARSE_SRC_PATH)/cbor/spec \
    $(EVERPARSE_SRC_PATH)/cbor/pulse \
    $(EVERPARSE_SRC_PATH)/cddl/spec \
    $(EVERPARSE_SRC_PATH)/cddl/pulse \
    $(EVERPARSE_SRC_PATH)/cddl/tool

ALREADY_CACHED := *,-$(MNAME),
FSTAR_DEP_OPTIONS := --extract $(MNAME)
FSTAR_FILES := $(OUTPUT_DIRECTORY)/$(MNAME).fst
CACHE_DIRECTORY := $(OUTPUT_DIRECTORY)
FSTAR_DEP_FILE := $(OUTPUT_DIRECTORY)/.depend

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(ALL_ML_FILES)

.PHONY: all extract
