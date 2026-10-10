all: extract

EVERPARSE_SRC_PATH := $(realpath ../..)
include $(EVERPARSE_SRC_PATH)/windows.Makefile

INCLUDE_PATHS += $(EVERPARSE_SRC_PATH)/cbor/spec $(EVERPARSE_SRC_PATH)/cddl/spec $(EVERPARSE_SRC_PATH)/cddl/pulse
FSTAR_FILES := $(EVERPARSE_SRC_PATH)/cddl/spec/CDDL.Spec.AST.Base.fst $(EVERPARSE_SRC_PATH)/cddl/spec/CDDL.Spec.AST.Print.fst $(EVERPARSE_SRC_PATH)/cddl/spec/CDDL.Spec.AST.Elab.fst $(EVERPARSE_SRC_PATH)/cddl/spec/CDDL.Spec.AST.Driver.fst CDDL.Tool.Gen.fst $(EVERPARSE_SRC_PATH)/cbor/spec/CBOR.Spec.Constants.fst
ALREADY_CACHED := *,
OUTPUT_DIRECTORY := ocaml/evercddl-lib/extracted
FSTAR_DEP_FILE := ocaml.depend

# The hand-written OCaml of evercddl-lib (CDDLParser.ml, ABNF.ml) builds and
# reads the CDDL AST directly, and evercddl-gen calls the printer and the
# generator, so every definition of those modules is a root: nothing in F*
# names them.
CUSTARD_BACKEND := OCaml
# The AST *types* rather than the whole of CDDL.Spec.AST.Base: rooting every
# definition of that module drags in its specification-only functions, and one
# of them (seq_is_bounded64) makes Custard compile FStar.Seq.Base, whose name
# then clashes with the FStar_Seq_Base of the fstar.lib this library links
# against -- and the two disagree about the representation of a seq.
CUSTARD_ENTRIES := CDDL.Spec.AST.Base.literal
CUSTARD_ENTRIES += CDDL.Spec.AST.Base.elem_typ
CUSTARD_ENTRIES += CDDL.Spec.AST.Base.group
CUSTARD_ENTRIES += CDDL.Spec.AST.Base.typ
CUSTARD_ENTRIES += CDDL.Spec.AST.Base.decl
CUSTARD_ENTRIES += CDDL.Spec.AST.Base.program
CUSTARD_ENTRIES += CDDL.Spec.AST.Elab.Base.mk_TChoice
CUSTARD_ENTRIES += CDDL.Spec.AST.Driver.mk_GChoice
CUSTARD_ENTRIES += CDDL.Spec.AST.Driver.mk_GConcat
CUSTARD_ENTRY_MODULES := CDDL.Spec.AST.Print
CUSTARD_ENTRY_MODULES += CDDL.Tool.Gen
CUSTARD_ENTRY_MODULES += CBOR.Spec.Constants
CUSTARD_ROOTS := CDDL.Tool.Gen.fst

include $(EVERPARSE_SRC_PATH)/common.Makefile

extract: $(CUSTARD_STAMP)

.PHONY: all extract

extract: $(OUTPUT_DIRECTORY)/Z3Version.ml

# After $(CUSTARD_STAMP), which empties the output directory of .ml files.
$(OUTPUT_DIRECTORY)/Z3Version.ml: $(CUSTARD_STAMP)
	rm -f $@ $@.tmp
	echo 'let z3_version = "$(EVERPARSE_Z3_VERSION)"' > $@.tmp
	mv $@.tmp $@
