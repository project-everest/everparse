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

GEN := ocaml/_build/default/gen_fst/Main.exe

TARGETS := dpe cose_sign cose_encrypt

MNAME_dpe          := RoundtripDpe
MNAME_cose_sign    := RoundtripCoseSign
MNAME_cose_encrypt := RoundtripCoseEncrypt

CDDLS_dpe          := $(EVERPARSE_SRC_PATH)/cddl/tests/dpe/dpe.cddl       $(EVERPARSE_SRC_PATH)/cddl/tests/dpe/dpe_postlude.cddl
CDDLS_cose_sign    := $(EVERPARSE_SRC_PATH)/cose/cose-sign.cddl           $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl
CDDLS_cose_encrypt := $(EVERPARSE_SRC_PATH)/cose/cose-encrypt.cddl        $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl

$(GEN): ocaml/dune-project ocaml/gen_fst/dune ocaml/gen_fst/Main.ml
	cd ocaml && dune build gen_fst/Main.exe

# Template instantiated once per target. Each instance writes only into
# $(ODIR)/$1, so `make -j` over distinct targets has no shared output.
define ROUNDTRIP_template

$(ODIR)/$1:
	mkdir -p $$@

$(ODIR)/$1/$(MNAME_$1).fst: $(GEN) $(CDDLS_$1) | $(ODIR)/$1
	$(GEN) $(MNAME_$1) $(ODIR)/$1 $(CDDLS_$1)

# Delegate F* typechecking and OCaml extraction to extract.Makefile,
# which uses the standard EverParse common.Makefile.
$(ODIR)/$1/$(MNAME_$1).ml: $(ODIR)/$1/$(MNAME_$1).fst extract.Makefile
	+$(MAKE) -f extract.Makefile MNAME=$(MNAME_$1) OUTPUT_DIRECTORY=$(ODIR)/$1

$(ODIR)/$1/check.exe: Check.ml $(ODIR)/$1/$(MNAME_$1).ml
	cp Check.ml $(ODIR)/$1/Check.ml
	printf 'let () = Check.run [%s] $(MNAME_$1).ast\n' '$(foreach f,$(CDDLS_$1),"$f"; )' > $(ODIR)/$1/main.ml
	cd $(ODIR)/$1 && ocamlfind ocamlopt -package evercddl.lib -linkpkg Check.ml $(MNAME_$1).ml main.ml -o check.exe

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
