# Roundtrip test: parse .cddl files with the OCaml parser, dump the
# resulting `program` value into a F* module via CDDL.Spec.AST.Print,
# extract that module to OCaml, then check that the extracted constant
# equals a fresh parser run on the same inputs.
#
# Three targets that can run in parallel: dpe, cose_sign, cose_encrypt.

all: test

EVERPARSE_SRC_PATH := $(realpath ../../..)
EVERPARSE_HOME     := $(realpath $(EVERPARSE_SRC_PATH)/..)
ODIR := _output

FSTAR_EXE ?= fstar.exe

# evercddl.lib (handwritten + extracted) lives under $EVERPARSE_HOME/lib;
# fstar.lib lives under the F* installation. `fstar.exe --ocamlenv` prepends
# the latter to OCAMLPATH for us.
export OCAMLPATH := $(EVERPARSE_HOME)/lib:$(OCAMLPATH)

FSTAR_OPTIONS := \
    --z3version 4.13.3 \
    --warn_error @241 \
    --cmi \
    --ext context_pruning \
    --cache_checked_modules

# Mirrors the include set used by cddl.exe so the extracted F* module
# (which only references CDDL.Spec.AST.Base) can find every .checked
# in its transitive closure.
FSTAR_INCLUDES := \
    --include $(EVERPARSE_SRC_PATH)/cbor/spec \
    --include $(EVERPARSE_SRC_PATH)/cbor/pulse \
    --include $(EVERPARSE_SRC_PATH)/cddl/spec \
    --include $(EVERPARSE_SRC_PATH)/cddl/pulse \
    --include $(EVERPARSE_SRC_PATH)/cddl/tool \
    --include $(KRML_HOME)/krmllib \
    --include $(KRML_HOME)/krmllib/obj \
    --include $(PULSE_HOME)/lib/pulse

GEN := ocaml/_build/default/gen_fst/Main.exe

TARGETS := dpe cose_sign cose_encrypt

MNAME_dpe          := RoundtripDpe
MNAME_cose_sign    := RoundtripCoseSign
MNAME_cose_encrypt := RoundtripCoseEncrypt

CDDLS_dpe          := $(EVERPARSE_SRC_PATH)/cddl/tests/dpe/dpe.cddl       $(EVERPARSE_SRC_PATH)/cddl/tests/dpe/dpe_postlude.cddl
CDDLS_cose_sign    := $(EVERPARSE_SRC_PATH)/cose/cose-sign.cddl           $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl
CDDLS_cose_encrypt := $(EVERPARSE_SRC_PATH)/cose/cose-encrypt.cddl        $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl

$(GEN): ocaml/dune-project ocaml/gen_fst/dune ocaml/gen_fst/Main.ml
	cd ocaml && $(FSTAR_EXE) --ocamlenv dune build gen_fst/Main.exe

# Template instantiated once per target. Each instance writes only into
# $(ODIR)/$1, so `make -j` over distinct targets has no shared output.
define ROUNDTRIP_template

$(ODIR)/$1:
	mkdir -p $$@

$(ODIR)/$1/$(MNAME_$1).fst: $(GEN) $(CDDLS_$1) | $(ODIR)/$1
	$(GEN) $(MNAME_$1) $(ODIR)/$1 $(CDDLS_$1)

$(ODIR)/$1/$(MNAME_$1).fst.checked: $(ODIR)/$1/$(MNAME_$1).fst
	$(FSTAR_EXE) $$< $(FSTAR_OPTIONS) $(FSTAR_INCLUDES) \
	    --already_cached '*,-$(MNAME_$1)' \
	    --cache_dir $(ODIR)/$1
	touch -c $$@

$(ODIR)/$1/$(MNAME_$1).ml: $(ODIR)/$1/$(MNAME_$1).fst.checked
	$(FSTAR_EXE) $(ODIR)/$1/$(MNAME_$1).fst $(FSTAR_OPTIONS) $(FSTAR_INCLUDES) \
	    --already_cached '*,' \
	    --cache_dir $(ODIR)/$1 --odir $(ODIR)/$1 \
	    --codegen OCaml --extract_module $(MNAME_$1)

$(ODIR)/$1/check.exe: Check.ml $(ODIR)/$1/$(MNAME_$1).ml
	cp Check.ml $(ODIR)/$1/Check.ml
	printf 'let () = Check.run [%s] $(MNAME_$1).ast\n' '$(foreach f,$(CDDLS_$1),"$f"; )' > $(ODIR)/$1/main.ml
	cd $(ODIR)/$1 && $(FSTAR_EXE) --ocamlenv ocamlfind ocamlopt -package evercddl.lib -linkpkg Check.ml $(MNAME_$1).ml main.ml -o check.exe

$1.run: $(ODIR)/$1/check.exe
	$$<

.PHONY: $1.run
endef

$(foreach t,$(TARGETS),$(eval $(call ROUNDTRIP_template,$t)))

test: $(addsuffix .run,$(TARGETS))

.PHONY: all test

clean:
	rm -rf $(ODIR)
	cd ocaml && dune clean 2>/dev/null || true

.PHONY: clean
