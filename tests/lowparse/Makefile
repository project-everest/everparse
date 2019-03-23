all: verify-all extract-all

FSTAR_OUT_DIR?=.fstar-out

ifndef FSTAR_HOME
  FSTAR_EXE=$(shell which fstar.exe)
  ifneq ($(.SHELLSTATUS),0)
    FSTAR_HOME=../../../FStar
  endif
endif
ifdef FSTAR_HOME
  FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
endif

ifndef KREMLIN_HOME
  KREMLIB=$(shell ocamlfind query kremlin)
  ifneq ($(.SHELLSTATUS),0)
    KREMLIN_HOME=../../../kremlin
  endif
endif
ifdef KREMLIN_HOME
  KREMLIB=$(KREMLIN_HOME)/kremlib
  KREMLIN_EXE=$(KREMLIN_HOME)/krml
else
  KREMLIN_EXE=krml
endif

INCLUDE_KREMLIN=--include $(KREMLIB)

FSTAR_OPTIONS += --use_hints --use_two_phase_tc true --include . # --use_extracted_interfaces

# NOTE: the cache dir and out dir for F* MUST be the same, because the
# .krml files should be generated only once.

MY_FSTAR=$(FSTAR_EXE) --cache_checked_modules --cache_dir $(FSTAR_OUT_DIR) --odir $(FSTAR_OUT_DIR) $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN)

INTERMEDIATE_LEVEL=LowParse_TestLib_SLow_c.c -ccopt -Wno-error-tautological-compare

LOW_LEVEL=LowParse_TestLib_Low_c.c

MY_KREMLIN=$(KREMLIN_EXE) -bundle 'LowParse.\*'  -add-include '"kremlin/internal/compat.h"'

EXAMPLES=Example Example2 Example3 Example5 Example6 Example7 Example8 Example9 Example10 Example11 Example12
ROOT_FILES=LowParse.SLow.fst LowParse.Low.fst $(addprefix LowParse, $(addsuffix .fst, $(EXAMPLES))) LowParse.TestLib.SLow.fst LowParse.TestLib.Low.fst

EXCLUDE_KRML_FILES=$(FSTAR_OUT_DIR)/prims.krml

EXAMPLE_DEPEND_FILES=$(addsuffix .depend,$(EXAMPLES))

$(EXAMPLE_DEPEND_FILES): %.depend: *.fst *.fsti
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full LowParse$(basename $@).fst > $@

clean:
	rm -rf $(FSTAR_OUT_DIR) $(EXAMPLES) $(addsuffix .depend, $(EXAMPLES)) .depend

.depend: $(EXAMPLE_DEPEND_FILES)
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) --dep full $(ROOT_FILES) > $@
	for f in $(EXAMPLES) ; do \
	 $(MAKE) EXCLUDE_KRML_FILES='$(EXCLUDE_KRML_FILES)' EXAMPLE=$$f -f Makefile.example ; \
	done

include .depend

verify-all: $(ALL_CHECKED_FILES)

$(FSTAR_OUT_DIR)/%.checked:
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) $<
	touch $@

ifdef ADMIT_LOWPARSE
$(FSTAR_OUT_DIR)/LowParse.%.checked: FSTAR_OPTIONS += --admit_smt_queries true
$(FSTAR_OUT_DIR)/LowParse.%.checked: OTHERFLAGS := $(filter-out --record_hints,$(OTHERFLAGS))
endif

# No need to specify the path to the .fst file, since it will be
# recovered by the --include path
#
# NOTE: I use --extract_module because
# '--extract LowParse.SLow' would actually extract the whole
# namespace, not only the module.
$(FSTAR_OUT_DIR)/%.krml:
	$(MY_FSTAR) $(FSTAR_OPTIONS) $(OTHERFLAGS) --codegen Kremlin $(notdir $(basename $<)) --extract_module $(notdir $(basename $(basename $<))) --warn_error '@241'
	touch $@

$(EXAMPLES): %: %/a.out

%/a.out:
	$(MY_KREMLIN) $(KREMLIN_ARGS) -tmpdir $(EXAMPLE) -bundle LowParse$(EXAMPLE)'.Aux' -warn-error '@2' -no-prefix LowParse$(EXAMPLE) $(EXAMPLE_KRML_FILES) -o $@
	$@

extract-all: $(EXAMPLES)

Example: KREMLIN_ARGS=$(INTERMEDIATE_LEVEL)
Example2: KREMLIN_ARGS=$(INTERMEDIATE_LEVEL)
Example3: KREMLIN_ARGS=$(LOW_LEVEL)
Example5: KREMLIN_ARGS=
Example6: KREMLIN_ARGS=
Example7: KREMLIN_ARGS=
Example8: KREMLIN_ARGS=$(LOW_LEVEL)
Example9: KREMLIN_ARGS=$(LOW_LEVEL)
Example10: KREMLIN_ARGS=
Example11: KREMLIN_ARGS=
Example12: KREMLIN_ARGS=

.PHONY: all verify-all clean extract-all $(EXAMPLES)

$(FSTAR_OUT_DIR)/FStar.Math.Lemmas.fst.checked: FSTAR_OPTIONS += --use_extracted_interfaces true

%.fst-in:
	@echo $(INCLUDE_KREMLIN) --cache_dir .fstar-out

%.fsti-in:
	@echo $(INCLUDE_KREMLIN)
