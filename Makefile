all: package-subset asn1 cbor cddl cbor-interface

export FSTAR_EXE ?= $(wildcard $(realpath opt)/FStar/bin/fstar.exe)
export KRML_HOME ?= $(realpath opt/karamel)
export PULSE_HOME ?= $(realpath opt/pulse/out)
export EVERPARSE_OPT_PATH=$(realpath opt)

include $(EVERPARSE_OPT_PATH)/env.Makefile

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
	+$(MAKE) -C doc 3d

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

test: all lowparse-test quackyducky-test 3d-test asn1-test

ifeq (,$(NO_PULSE))
lowparse-pulse: $(filter src/lowparse/pulse/%,$(ALL_CHECKED_FILES))
else
lowparse-pulse:
endif

.PHONY: lowparse-pulse

cbor:
	+$(MAKE) -C src/cbor/pulse/det

cbor-interface: $(filter-out src/cbor/spec/raw/%,$(filter src/cbor/spec/%,$(ALL_CHECKED_FILES)))

ifeq (,$(NO_PULSE))
cbor-interface: $(filter-out src/cbor/pulse/raw/%,$(filter src/cbor/pulse/%,$(ALL_CHECKED_FILES)))
endif

.PHONY: cbor-interface

cbor-det-c-test: cbor
	+$(MAKE) -C src/cbor/pulse/det/c/test

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

cddl-tool: cddl-pulse $(filter src/cddl/tool/%,$(ALL_CHECKED_FILES))
	+$(MAKE) -C src/cddl/tool
else
cddl-tool:
endif

cddl: cbor cbor-interface cddl-spec cddl-tool

.PHONY: cddl-spec cddl-tool

.PHONY: cbor cbor-det-c-test cbor-det-rust-test cbor-test cddl

ifeq (,$(NO_PULSE))
cddl-plugin-test: cddl
	+$(MAKE) -C src/cddl/test
else
cddl-plugin-test:
endif

.PHONY: cddl-plugin-test

ifeq (,$(NO_PULSE))
cddl-demo: cddl
	+$(MAKE) -C src/cddl/demo
else
cddl-demo:
endif

.PHONY: cddl-demo

ifeq (,$(NO_PULSE))
cddl-unit-tests: cddl
	+$(MAKE) -C src/cddl/unit-tests
else
cddl-unit-tests:
endif

.PHONY: cddl-unit-tests

ifeq (,$(NO_PULSE))
# cbor-extract-pre needed because Rust extraction extracts CBOR and COSE altogether
cose-extract-test: cddl cbor-extract-pre
	+$(MAKE) -C src/cose test-extract

# This rule is incompatible with cose-extract-test
# cbor-extract-pre needed because Rust extraction extracts CBOR and COSE altogether
cose-snapshot: cddl cbor-extract-pre
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

cose:
	+$(MAKE) -C src/cose

.PHONY: cose

cddl-test: cddl cddl-plugin-test cddl-demo cose-extract-test cddl-unit-tests

.PHONY: cddl-test

ci: test lowparse-pulse cbor-test cddl-test

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
