# everparse-asn1: build, to $(EVERPARSE_HOME)/bin/everparse-asn1.exe.
# Prerequisites: OCaml with dune (e.g. the opam switch of EverParse).
# The tests are in share/everparse/tests/asn1/tool.

all: build

EVERPARSE_HOME ?= $(realpath ../../..)
DUNE ?= dune
TOOL := $(EVERPARSE_HOME)/bin/everparse-asn1.exe

include $(EVERPARSE_HOME)/lib/everparse/z3-version.Makefile

# The Z3 version that the tool asks F* for, as for EverCDDL
Z3VERSION_ML := ocaml/everparse-asn1/Z3Version.ml

$(Z3VERSION_ML): $(EVERPARSE_HOME)/lib/everparse/z3-version.Makefile
	echo 'let z3_version = "$(EVERPARSE_Z3_VERSION)"' > $@.tmp
	mv $@.tmp $@

$(TOOL): $(Z3VERSION_ML) $(wildcard ocaml/dune-project ocaml/everparse-asn1/*.ml ocaml/everparse-asn1/*.mll ocaml/everparse-asn1/dune)
	cd ocaml && $(DUNE) build
	mkdir -p $(dir $@)
	cp ocaml/_build/install/default/bin/everparse-asn1.exe $@
	chmod +w $@ # because dune produces read-only executables

build: $(TOOL)

clean:
	rm -rf _output $(Z3VERSION_ML)
	cd ocaml && $(DUNE) clean

.PHONY: all build clean
