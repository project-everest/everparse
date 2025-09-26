# NOTE: if you want to add global F* options, you need to do the following:
# 1. Add them to FSTAR_OPTIONS in src/fstar.Makefile
# 2. Add them to fstar_args0 in src/3d/ocaml/Batch.ml

all: package-subset asn1 cbor cddl cbor-interface cose

export EVERPARSE_OPT_PATH=$(realpath opt)
export FSTAR_EXE ?= $(wildcard $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe)
export KRML_HOME ?= $(EVERPARSE_OPT_PATH)/karamel
export PULSE_HOME ?= $(EVERPARSE_OPT_PATH)/pulse/out
EVEREST_HOME ?= $(EVERPARSE_OPT_PATH)/everest
export PATH := $(EVERPARSE_OPT_PATH)/z3:$(PATH)

include $(EVERPARSE_OPT_PATH)/env.Makefile

$(EVERPARSE_OPT_PATH)/everest:
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) everest

_opam: $(EVEREST_HOME)
	rm -rf $@.tmp
	if opam init --bare --no-setup && opam switch create ./ ocaml-base-compiler.5.3.0 && opam exec $(EVEREST_HOME)/everest opam ; then true ; else mv $@ $@.tmp ; exit 1 ; fi

package-subset: quackyducky lowparse 3d

.PHONY: package-subset

EVERPARSE_SRC_PATH = $(realpath src)

ALREADY_CACHED := *,-LowParse,-EverParse3d,-ASN1,-CBOR,-CDDL,

SRC_DIRS += src/lowparse src/ASN1 src/3d/prelude src/cbor/spec src/cbor/spec/raw src/cbor/spec/raw/everparse src/cddl/spec

ifeq (,$(NO_PULSE))
  SRC_DIRS += src/lowparse/pulse src/cbor/pulse src/cbor/pulse/raw src/cbor/pulse/raw/everparse src/cddl/pulse src/cddl/tool
endif

ifneq (,$(FSTAR_EXE))

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
ifeq (,$(NO_PULSE))
  include $(EVERPARSE_SRC_PATH)/pulse.Makefile
endif
include $(EVERPARSE_SRC_PATH)/common.Makefile

endif

lowparse: $(filter-out src/lowparse/pulse/%,$(filter src/lowparse/%,$(ALL_CHECKED_FILES)))

ifeq (,$(NO_PULSE))
lowparse: $(filter src/lowparse/pulse/%,$(ALL_CHECKED_FILES))
endif

# lowparse needed because of .fst behind .fsti for extraction
3d-prelude: $(filter src/3d/prelude/%,$(ALL_CHECKED_FILES)) $(filter-out src/lowparse/LowParse.SLow.% src/lowparse/pulse/%,$(filter src/lowparse/%,$(ALL_CHECKED_FILES)))
	+$(MAKE) -C src/3d prelude

.PHONY: 3d-prelude

3d-exe:
	+$(MAKE) -C src/3d 3d

.PHONY: 3d-exe

3d: 3d-prelude 3d-exe

# filter-out comes from NOT_INCLUDED in src/ASN1/Makefile
asn1: $(filter-out $(addprefix src/ASN1/,$(addsuffix .checked,ASN1.Tmp.fst ASN1.Test.Interpreter.fst ASN1.Low.% ASN1Test.fst ASN1.bak%)),$(filter src/ASN1/%,$(ALL_CHECKED_FILES)))

quackyducky:
	+$(MAKE) -C src/qd

bin/qd.exe: quackyducky

.gen-test.touch: bin/qd.exe tests/unittests.rfc tests/bitcoin.rfc
	rm -f tests/unit/*.fst tests/unit/*.fsti
	bin/qd.exe -odir tests/unit tests/unittests.rfc
	bin/qd.exe -low -odir tests/unit tests/bitcoin.rfc
	touch $@

gen-test: .gen-test.touch

lowparse-unit-test: lowparse
	+$(MAKE) -C tests/lowparse

3d-unit-test: 3d
	+$(MAKE) -C src/3d test

3d-doc-test: 3d
	+$(MAKE) -C doc 3d-test

3d-test: 3d-unit-test 3d-doc-test

asn1-test: asn1
	+$(MAKE) -C src/ASN1 test

lowparse-bitfields-test: lowparse
	+$(MAKE) -C tests/bitfields

lowparse-test: lowparse-unit-test lowparse-bitfields-test

quackyducky-unit-test: gen-test lowparse
	+$(MAKE) -C tests/unit

quackyducky-sample-test: quackyducky lowparse
	+$(MAKE) -C tests/sample

quackyducky-sample-low-test: quackyducky lowparse
	+$(MAKE) -C tests/sample_low

quackyducky-sample0-test: quackyducky lowparse
	+$(MAKE) -C tests/sample0

quackyducky-test: quackyducky-unit-test quackyducky-sample-test quackyducky-sample0-test quackyducky-sample-low-test

test: all lowparse-test quackyducky-test 3d-test asn1-test cbor-test cddl-test cose-test

submodules:
	$(MAKE) -C $(EVERPARSE_OPT_PATH) submodules

.PHONY: submodules

cbor:
	+$(MAKE) -C src/cbor/pulse/det

cbor-interface: $(filter-out src/cbor/spec/raw/%,$(filter src/cbor/spec/%,$(ALL_CHECKED_FILES)))

ifeq (,$(NO_PULSE))
cbor-interface: $(filter-out src/cbor/pulse/raw/%,$(filter src/cbor/pulse/%,$(ALL_CHECKED_FILES)))
endif

.PHONY: cbor-interface

cbor-det-c-test: cbor
	+$(MAKE) -C src/cbor/pulse/det/c all-tests

ifeq (,$(NO_PULSE))
cbor-det-c-vertest: cbor cbor-interface
	+$(MAKE) -C src/cbor/pulse/det/vertest/c
else
cbor-det-c-vertest:
endif

.PHONY: cbor-det-c-vertest

ifeq (,$(NO_PULSE))
cbor-det-common-vertest: cbor cbor-interface
	+$(MAKE) -C src/cbor/pulse/det/vertest/common
else
cbor-det-common-vertest:
endif

.PHONY: cbor-det-common-vertest

# NOTE: I wish we could use `cargo -C ...` but see https://github.com/rust-lang/cargo/pull/11960
cbor-det-rust-test: cbor
	+cd src/cbor/pulse/det/rust && cargo test

cbor-verify: $(filter src/cbor/spec/%,$(ALL_CHECKED_FILES))

ifeq (,$(NO_PULSE))
cbor-verify: $(filter src/cbor/pulse/%,$(ALL_CHECKED_FILES))
endif

.PHONY: cbor-verify

# lowparse needed for extraction because of .fst files behind .fsti
ifeq (,$(NO_PULSE))
cbor-extract-pre: cbor-verify $(filter-out src/lowparse/LowParse.SLow.% src/lowparse/LowParse.Low.%,$(filter src/lowparse/%,$(ALL_CHECKED_FILES)))

.PHONY: cbor-extract-pre

cbor-test-snapshot: cbor-extract-pre
	+$(MAKE) -C src/cbor test-snapshot
else
cbor-test-snapshot: cbor-verify
endif

.PHONY: cbor-test-snapshot

# This rule is incompatible with `cbor` and `cbor-test-snapshot`
ifeq (,$(NO_PULSE))
cbor-snapshot: cbor-extract-pre
	+$(MAKE) -C src/cbor snapshot
else
cbor-snapshot:
endif

.PHONY: cbor-snapshot

cbor-test-unverified: cbor-det-c-test cbor-det-rust-test

.PHONY: cbor-test-unverified

cbor-test-verified: cbor-det-c-vertest cbor-det-common-vertest

.PHONY: cbor-test-verified

cbor-test-extracted: cbor-test-unverified cbor-test-verified

.PHONY: cbor-test-extracted

cbor-test: cbor-test-extracted cbor-test-snapshot

cddl-spec: $(filter src/cddl/spec/%,$(ALL_CHECKED_FILES))

ifeq (,$(NO_PULSE))
cddl-pulse: cddl-spec $(filter src/cddl/pulse/%,$(ALL_CHECKED_FILES))

# cbor-extract-pre needed because Rust extraction extracts CBOR and COSE altogether
cddl-tool: cddl-pulse $(filter src/cddl/tool/%,$(ALL_CHECKED_FILES)) cbor-extract-pre
	+$(MAKE) -C src/cddl/tool
else
cddl-tool:
endif

cddl: cbor cbor-interface cddl-spec cddl-tool

.PHONY: cddl-spec cddl-tool

.PHONY: cbor cbor-det-c-test cbor-det-rust-test cbor-test cddl

ifeq (,$(NO_PULSE))
cddl-unit-tests: cddl
	+$(MAKE) -C src/cddl test
else
cddl-unit-tests:
endif

.PHONY: cddl-unit-tests

ifeq (,$(NO_PULSE))
cose-extract-test: cddl
	+$(MAKE) -C src/cose test-extract

# This rule is incompatible with cose-extract-test
cose-snapshot: cddl
	+$(MAKE) -C src/cose snapshot
else
cose-extract-test:
cose-snapshot:
endif

.PHONY: cose-extract-test cose-snapshot

cose-extracted-test: cose
	+$(MAKE) -C src/cose test-extracted

.PHONY: cose-extracted-test

cose-test: cose-extract-test cose-extracted-test

.PHONY: cose-test

cose: cbor
	+$(MAKE) -C src/cose

.PHONY: cose

cddl-test: cddl cddl-unit-tests

.PHONY: cddl-test

ci: test 3d-doc-ci

# cbor needed because we regenerate its Rust documentation
3d-doc-ci: 3d-doc-test cbor
	+$(MAKE) -C doc 3d-ci

.PHONY: 3d-doc-ci

3d-doc-snapshot: 3d
	+$(MAKE) -C doc 3d-snapshot

.PHONY: 3d-doc-snapshot

clean-3d:
	+$(MAKE) -C src/3d clean

clean-lowparse:
	+$(MAKE) -C src/lowparse clean

clean-quackyducky:
	+$(MAKE) -C src/qd clean

clean: clean-3d clean-lowparse clean-quackyducky
	rm -rf bin

.PHONY: all gen verify test gen-test clean quackyducky lowparse lowparse-test quackyducky-test lowparse-fstar-test quackyducky-sample-test quackyducky-sample0-test quackyducky-unit-test package 3d 3d-test lowparse-unit-test lowparse-bitfields-test release everparse 3d-unit-test 3d-doc-test ci clean-3d clean-lowparse clean-quackyducky asn1 asn1-test

release package package-noversion nuget-noversion everparse:
	+$(MAKE) -f package.Makefile $@

# For F* testing purposes, cf. FStarLang/FStar@fc30456a163c749843c50ee5f86fa22de7f8ad7a

lowparse-fstar-test:
	+$(MAKE) -C src/lowparse fstar-test
