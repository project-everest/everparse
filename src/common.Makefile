ifeq (,$(EVERPARSE_SRC_PATH))
  $(error "EVERPARSE_SRC_PATH must be set to the absolute path of the src/ subdirectory of the EverParse repository")
endif

include $(EVERPARSE_SRC_PATH)/fstar.Makefile

# Clean rules (excluding clean itself)
clean_rules += clean-checked clean-krml clean-ml clean-depend
other_clean_rules += clean

# List the directories of all root files
SRC_DIRS += .

# List additional include paths
INCLUDE_PATHS += $(SRC_DIRS)

# A place to put all build artifacts
ifneq (,$(OUTPUT_DIRECTORY))
ifeq ($(OS),Windows_NT)
  OUTPUT_DIRECTORY := $(shell cygpath -m $(OUTPUT_DIRECTORY))
endif
  FSTAR_OPTIONS += --odir $(OUTPUT_DIRECTORY)
endif

# A place to put .checked files. If this variable is left empty, then
# each .checked file will be generated right next to its corresponding
# source file.
ifneq (,$(CACHE_DIRECTORY))
ifeq ($(OS),Windows_NT)
  CACHE_DIRECTORY := $(shell cygpath -m $(CACHE_DIRECTORY))
endif
  FSTAR_OPTIONS += --cache_dir $(CACHE_DIRECTORY)
  INCLUDE_PATHS+=$(CACHE_DIRECTORY)
endif

# Uncomment the definition of PROFILE below, if you want some basic
# profiling of F* runs It will report the time spent
# on typechecking your file And the time spent in SMT, which is
# included in the total typechecking time

# PROFILE=--profile YOUR_FILE --profile_component 'FStar.Universal.tc_source_file FStar.SMTEncoding'
FSTAR_OPTIONS += $(PROFILE)

# List the roots from where all dependencies are computed
ifeq ($(OS),Windows_NT)
SRC_DIRS := $(shell cygpath -m $(SRC_DIRS))
endif
FSTAR_FILES ?= $(wildcard $(addsuffix /*.fst,$(SRC_DIRS)) $(addsuffix /*.fsti,$(SRC_DIRS)))

# `ALREADY_CACHED` expected to be empty or to end with a comma
ifeq ($(OS),Windows_NT)
INCLUDE_PATHS := $(shell cygpath -m $(INCLUDE_PATHS))
endif
FSTAR_OPTIONS += $(OTHERFLAGS) $(addprefix --include ,$(INCLUDE_PATHS)) --cache_checked_modules --warn_error @241 --already_cached $(ALREADY_CACHED)Prims,FStar,LowStar --ext context_pruning

# https://github.com/FStarLang/FStar/pull/3861
# FSTAR_OPTIONS += --ext optimize_let_vc

# Passing RESOURCEMONITOR=1 will create .runlim files through the source tree with
# information about the time and space taken by each F* invocation.
ifneq ($(RESOURCEMONITOR),)
	ifeq ($(shell which runlim),)
		_ := $(error $(NO_RUNLIM_ERR)))
	endif
	ifneq ($(MONID),)
		MONPREFIX=$(MONID).
	endif
	RUNLIM=runlim -p -o $@.$(MONPREFIX)runlim
endif

FSTAR_EXE ?= fstar.exe

FSTAR=$(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

FSTAR_DEP_FILE ?= .depend

$(FSTAR_DEP_FILE): $(FSTAR_FILES)
	$(call msg, "DEPEND")
ifneq (,$(OUTPUT_DIRECTORY))
	mkdir -p $(OUTPUT_DIRECTORY)
endif
ifneq (,$(CACHE_DIRECTORY))
	mkdir -p $(CACHE_DIRECTORY)
endif
	if test -n "$(dir $@)" ; then mkdir -p "$(dir $@)" ; fi
	rm -f $@.rsp
	for f in $(FSTAR_FILES) ; do echo $$f ; done > $@.rsp
	$(Q)$(FSTAR) $(FSTAR_DEP_OPTIONS) --dep full @$@.rsp --output_deps_to $@.aux
	mv $@.aux $@

ifeq (,$(filter $(clean_rules) $(other_clean_rules),$(MAKECMDGOALS)))
include $(FSTAR_DEP_FILE)
endif

$(ALL_CHECKED_FILES): %.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(Q)$(RUNLIM) $(FSTAR) $(SIL) $(COMPAT_INDEXED_EFFECTS) $(if $(filter 1,$(ADMIT)),--admit_smt_queries true,) $<
	touch -c $@

verify: $(ALL_CHECKED_FILES)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

# Extraction
#
# All code generation goes through Custard, F*'s whole-program extractor
# (doc/ref/custard.md in the F* tree). Custard reads the checked files of the
# entire program in one run, so there is one rule rather than one rule per
# generated file, and its prerequisite is every .checked file: --dep describes
# what the old per-module backends read, which does not pin down what a
# whole-program extractor reads.
#
# The caller sets:
#   CUSTARD_BACKEND       -- OCaml (default), FSharp, KrmlC or KrmlRust
#   CUSTARD_ENTRY_MODULES -- modules every top-level definition of which is a
#                            root of the extraction (what --extract_module was)
#   CUSTARD_ENTRIES       -- individual roots, as dotted names
#   CUSTARD_ROOTS         -- the F* files named on the command line
#                            (default: $(FSTAR_FILES))
#   CUSTARD_REALIZED_MODULES -- OCaml only: modules realized by a hand-written
#                            .ml file of the same name
# and may add flags through CUSTARD_FLAGS.
#
# Dead code elimination is by reachability from the roots, so a module that
# nothing names and nothing reaches is not emitted at all; this is why every
# backend below has to say what its public surface is.

CUSTARD_BACKEND ?= OCaml
CUSTARD_ROOTS ?= $(FSTAR_FILES)

CUSTARD_FLAGS += --codegen Custard --custard_backend $(CUSTARD_BACKEND)
# One output file per F* source module. On the karamel backends that grouping
# is what -bundle and -no-prefix select on; on OCaml it is what lets
# hand-written .ml files sit beside the generated ones. The F# backend emits
# one whole program and has no split.
ifneq (FSharp,$(CUSTARD_BACKEND))
CUSTARD_FLAGS += --custard_split
endif
CUSTARD_FLAGS += $(addprefix --custard_entry_module ,$(CUSTARD_ENTRY_MODULES))
CUSTARD_FLAGS += $(addprefix --custard_entry ,$(CUSTARD_ENTRIES))
CUSTARD_FLAGS += $(addprefix --custard_extern_type ,$(CUSTARD_EXTERN_TYPES))

CUSTARD_OUTPUT_PREFIX := $(if $(OUTPUT_DIRECTORY),$(OUTPUT_DIRECTORY)/,)

CUSTARD = $(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS) $(CUSTARD_FLAGS)

# The karamel backends write a single .krml holding one karamel file per F*
# module; the others write into $(OUTPUT_DIRECTORY) and are tracked by a stamp.
CUSTARD_KRML := $(CUSTARD_OUTPUT_PREFIX)Custard.krml
CUSTARD_STAMP := $(CUSTARD_OUTPUT_PREFIX).custard.stamp

# The makefiles are a prerequisite because the roots, the backend and the
# extern types are given there: changing any of them changes the output.
CUSTARD_MAKEFILES := $(filter-out $(FSTAR_DEP_FILE),$(MAKEFILE_LIST))

$(CUSTARD_KRML): $(ALL_CHECKED_FILES) $(CUSTARD_MAKEFILES)
	$(call msg, "CUSTARD", $(CUSTARD_BACKEND))
	$(Q)$(CUSTARD) $(CUSTARD_ROOTS) -o $@

$(CUSTARD_STAMP): $(ALL_CHECKED_FILES) $(CUSTARD_MAKEFILES)
	$(call msg, "CUSTARD", $(CUSTARD_BACKEND))
	rm -f $(CUSTARD_OUTPUT_PREFIX)*.ml
	$(Q)$(CUSTARD) $(CUSTARD_ROOTS)
# Custard's notion of a realized module (section 8.2) is a hard-coded list of
# FStar.* modules, so an interface-only module of ours gets a file declaring
# its abstract types, which the hand-written realization also declares. Every
# value of such a module is an external, printed at its use sites and not
# declared, so the file holds nothing but those types: dropping it leaves the
# realization as the whole module. The check keeps that assumption honest.
	$(Q)for m in $(CUSTARD_REALIZED_MODULES) ; do \
	  f=$(CUSTARD_OUTPUT_PREFIX)$$m.ml ; \
	  if grep -q '^\(let\|exception\)' $$f ; then \
	    echo "$$f is not only type declarations: $$m cannot be realized by hand" ; \
	    exit 1 ; \
	  fi ; \
	  rm -f $$f ; \
	done
	touch $@

.PHONY: all verify %.fst-in %.fsti-in

clean-checked:
ifneq (,$(CACHE_DIRECTORY))
	rm -f $(CACHE_DIRECTORY)/*.checked
endif
	rm -f *.checked

.PHONY: clean-checked

clean-krml:
ifneq (,$(OUTPUT_DIRECTORY))
	rm -f $(OUTPUT_DIRECTORY)/*.krml
endif
	rm -f *.krml

.PHONY: clean-krml

clean-ml:
ifneq (,$(OUTPUT_DIRECTORY))
	rm -f $(OUTPUT_DIRECTORY)/*.ml
endif
	rm -f *.ml $(CUSTARD_STAMP)

.PHONY: clean-ml

clean-depend:
	rm -f $(FSTAR_DEP_FILE) $(FSTAR_DEP_FILE).aux $(FSTAR_DEP_FILE).rsp

.PHONY: clean-depend

clean: $(clean_rules)

.PHONY: clean
