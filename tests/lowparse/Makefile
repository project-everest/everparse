all: verify-all extract-all

EVERPARSE_SRC_PATH ?= $(realpath ../../src)

LOWPARSE_HOME ?= ../../src/lowparse

FSTAR_OUT_DIR?=.fstar-out

FSTAR_EXE ?= fstar.exe

include $(EVERPARSE_SRC_PATH)/fstar.Makefile

ifndef KRML_HOME
  KRMLLIB:=$(shell ocamlfind query karamel)
  ifneq ($(.SHELLSTATUS),0)
    KRML_HOME=../../../karamel
  endif
endif
ifdef KRML_HOME
  KRMLLIB:=$(KRML_HOME)/krmllib
  KRML_EXE=$(KRML_HOME)/krml
else
  KRML_EXE=krml
endif

INCLUDE_KRML=--include $(KRMLLIB) --include $(KRMLLIB)/obj

FSTAR_OPTIONS += --use_hints --trivial_pre_for_unannotated_effectful_fns false --include $(LOWPARSE_HOME) --already_cached +Prims,+FStar,+LowStar,+C,+Spec.Loops,+LowParse --cache_checked_modules --cache_dir $(FSTAR_OUT_DIR) --odir $(FSTAR_OUT_DIR) $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KRML) --cmi

# NOTE: the cache dir and out dir for F* MUST be the same, because the
# .krml files should be generated only once.

INTERMEDIATE_LEVEL=$(LOWPARSE_HOME)/LowParse_TestLib_SLow_c.c -ccopt -Wno-error-tautological-compare

LOW_LEVEL=$(LOWPARSE_HOME)/LowParse_TestLib_Low_c.c

MY_KRML=$(KRML_EXE) -fstar $(FSTAR_EXE) -bundle 'LowParse.\*'  -add-include '"krml/internal/compat.h"'

EXAMPLES=Example Example2 Example3 Example5 Example6 Example7 Example8 Example9 Example10 Example11 Example12 ExampleMono ExamplePair ExampleDepLen ExampleConstInt32le

NOEXTRACT_EXAMPLES=ExamplePair
ROOT_FILES=$(addprefix LowParse, $(addsuffix .fst, $(EXAMPLES)))

EXCLUDE_KRML_FILES=$(FSTAR_OUT_DIR)/prims.krml

EXAMPLE_DEPEND_FILES=$(addsuffix .depend,$(EXAMPLES))

$(EXAMPLE_DEPEND_FILES): %.depend: *.fst *.fsti
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full LowParse$(basename $@).fst --output_deps_to $@

clean:
	rm -rf $(FSTAR_OUT_DIR) $(EXAMPLES) $(addsuffix .depend, $(EXAMPLES)) .depend

.depend: $(EXAMPLE_DEPEND_FILES)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(ROOT_FILES) --output_deps_to $@
	# GM: This chunk below seems ill-placed. And if anything below fails
	# the target .depend is still created. At least slap a:
	#   ... || (rm -f $@; exit 1)
	# at the end?
	for f in $(EXAMPLES) ; do \
	 $(MAKE) EXCLUDE_KRML_FILES='$(EXCLUDE_KRML_FILES)' EXAMPLE=$$f -f Makefile.example ; \
	done

ifeq (,$(filter clean,$(MAKECMDGOALS)))
include .depend
endif

verify-all: $(ALL_CHECKED_FILES)

$(FSTAR_OUT_DIR)/%.checked:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

# No need to specify the path to the .fst file, since it will be
# recovered by the --include path
#
# NOTE: I use --extract_module because
# '--extract LowParse.SLow' would actually extract the whole
# namespace, not only the module.
$(FSTAR_OUT_DIR)/%.krml:
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(OTHERFLAGS) --codegen krml $(notdir $(basename $<)) --extract_module $(notdir $(basename $(basename $<))) --warn_error '@241'
	touch $@

$(EXAMPLES): %: %/a.out

%/a.out:
	$(MY_KRML) -fstar $(FSTAR_EXE) $(KRML_ARGS) -tmpdir $(EXAMPLE) -bundle LowParse$(EXAMPLE)'.Aux' -warn-error '@2' -no-prefix LowParse$(EXAMPLE) $(EXAMPLE_KRML_FILES) -o $@
	$@

extract-all: $(filter-out $(NOEXTRACT_EXAMPLES), $(EXAMPLES))

Example: KRML_ARGS=$(INTERMEDIATE_LEVEL)
Example2: KRML_ARGS=$(INTERMEDIATE_LEVEL)
Example3: KRML_ARGS=$(LOW_LEVEL)
Example5: KRML_ARGS=
Example6: KRML_ARGS=
Example7: KRML_ARGS=
Example8: KRML_ARGS=$(LOW_LEVEL)
Example9: KRML_ARGS=$(LOW_LEVEL)
Example10: KRML_ARGS=
Example11: KRML_ARGS=
Example12: KRML_ARGS=
ExampleMono: KRML_ARGS=
ExamplePair: KRML_ARGS=
ExampleDepLen: KRML_ARGS=
ExampleConstInt32le: KRML_ARGS=

.PHONY: all verify-all clean extract-all $(EXAMPLES) %.fst-in %.fsti-in

%.fst-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)

%.fsti-in:
	@echo $(FSTAR_OPTIONS) $(OTHERFLAGS)
