#NOTE: if you want to add global F* options, you need to do the following:
# 1. Add them to FSTAR_OPTIONS in src/fstar.Makefile
# 2. Add them to fstar_args0 in src/3d/ocaml/Batch.ml

all: package-subset asn1 cbor

.PHONY: all

package-subset: quackyducky lowparse 3d

.PHONY: package-subset

clean_rules += clean-3d clean-lowparse clean-quackyducky clean-cbor-verify clean-cddl clean-bin clean-cose-test clean-asn1 clean-tests clean-3d-tests clean-doc
other_clean_rules += distclean

include nofstar.Makefile

include deps.Makefile

ifneq ($(OS),Windows_NT)
package-subset: cddl
endif

# Disable COSE on MacOS because we don't know how to link with OpenSSL
ifneq ($(OS),Darwin)
all: cose
endif

ifeq (,$(NO_PULSE))
all: cddl cbor-interface
endif

EVERPARSE_SRC_PATH := $(realpath src)

ALREADY_CACHED := *,-LowParse,-EverParse3d,-ASN1,-CBOR,-CDDL,

SRC_DIRS += src/lowparse src/ASN1 src/3d/prelude src/cbor/spec src/cbor/spec/raw src/cbor/spec/raw/everparse src/cddl/spec

ifeq (,$(NO_PULSE))
  SRC_DIRS += src/lowparse/pulse src/cbor/pulse src/cbor/pulse/raw src/cbor/pulse/raw/everparse src/cddl/pulse src/cddl/tool
endif

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
ifeq (,$(NO_PULSE))
  include $(EVERPARSE_SRC_PATH)/pulse.Makefile
endif
include $(EVERPARSE_SRC_PATH)/common.Makefile

$(FSTAR_DEP_FILE): $(NEED_FSTAR) $(NEED_KRML) $(NEED_PULSE)

$(ALL_CHECKED_FILES): %.checked: $(NEED_FSTAR) $(NEED_Z3) $(NEED_KRML) $(NEED_PULSE)

ifeq (1,$(ADMIT_LOWPARSE))
$(filter src/lowparse/%,$(ALL_CHECKED_FILES)): ADMIT := 1
endif

ifeq (1,$(ADMIT_CBOR_CDDL))
$(filter src/cbor/% src/cddl/%,$(ALL_CHECKED_FILES)): ADMIT := 1
endif

lowparse: $(filter-out src/lowparse/pulse/%,$(filter src/lowparse/%,$(ALL_CHECKED_FILES)))

ifeq (,$(NO_PULSE))
lowparse: $(filter src/lowparse/pulse/%,$(ALL_CHECKED_FILES))
endif

# lowparse needed because of .fst behind .fsti for extraction
3d-prelude: $(filter src/3d/prelude/%,$(ALL_CHECKED_FILES)) $(filter-out src/lowparse/LowParse.SLow.% src/lowparse/pulse/%,$(filter src/lowparse/%,$(ALL_CHECKED_FILES)))
	+$(MAKE) -C src/3d/prelude

.PHONY: 3d-prelude

3d-exe: $(NEED_Z3)
	+$(MAKE) -C src/3d 3d

.PHONY: 3d-exe

3d: 3d-prelude 3d-exe

# filter-out comes from NOT_INCLUDED in src/ASN1/Makefile
asn1: $(filter-out $(addprefix src/ASN1/,$(addsuffix .checked,ASN1.Tmp.fst ASN1.Test.Interpreter.fst ASN1.Low.% ASN1Test.fst ASN1.bak%)),$(filter src/ASN1/%,$(ALL_CHECKED_FILES)))

quackyducky: qd-exe lowparse

qd-exe: $(NEED_OPAM)
	+$(MAKE) -C src/qd

.PHONY: qd-exe

lowparse-unit-test: lowparse
	+$(MAKE) -C tests/lowparse

3d-unit-test: 3d $(NEED_Z3_TESTGEN)
	+$(MAKE) -C src/3d test

3d-doc-test: 3d $(NEED_Z3_TESTGEN)
	+$(MAKE) -C doc 3d-test

3d-test: 3d-unit-test 3d-doc-test

asn1-test: asn1
	+$(MAKE) -C src/ASN1 test

lowparse-bitfields-test: lowparse
	+$(MAKE) -C tests/bitfields

ifeq (,$(NO_PULSE))
lowparse-pulse-test:
else
lowparse-pulse-test: lowparse
	+$(MAKE) -C tests/pulse
endif

.PHONY: lowparse-pulse-test

lowparse-test: lowparse-unit-test lowparse-bitfields-test lowparse-pulse-test

quackyducky-test: quackyducky
	+$(MAKE) -C tests

test: all lowparse-test quackyducky-test asn1-test cbor-test cddl-test

# Disable 3d-unit-test on MacOS because there is a loop in Makefiles
# Disable 3d-doc-test on MacOS because sphinx is not available
ifneq ($(OS),Darwin)
test: 3d-test
endif

# Disable COSE tests on MacOS because we don't know how to link with OpenSSL
ifneq ($(OS),Darwin)
test: cose-test
endif

submodules:
	$(MAKE) -C $(EVERPARSE_OPT_PATH) submodules

.PHONY: submodules

cbor-interface: $(filter-out src/cbor/spec/raw/%,$(filter src/cbor/spec/%,$(ALL_CHECKED_FILES)))

ifeq (,$(NO_PULSE))
cbor-interface: $(filter-out src/cbor/pulse/raw/%,$(filter src/cbor/pulse/%,$(ALL_CHECKED_FILES)))
endif

.PHONY: cbor-interface

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

cbor-verify: $(filter src/cbor/spec/%,$(ALL_CHECKED_FILES))

ifeq (,$(NO_PULSE))
cbor-verify: $(filter src/cbor/pulse/%,$(ALL_CHECKED_FILES))
endif

.PHONY: cbor-verify

# lowparse needed for extraction because of .fst files behind .fsti
ifeq (,$(NO_PULSE))
cbor-extract-pre: cbor-verify $(filter-out src/lowparse/LowParse.SLow.% src/lowparse/LowParse.Low.%,$(filter src/lowparse/%,$(ALL_CHECKED_FILES)))

.PHONY: cbor-extract-pre

cbor-extract-krml: cbor-extract-pre
	+$(MAKE) -C src/cbor extract-krml

.PHONY: cbor-extract-krml

cbor-test-snapshot: cbor-extract-krml
	+$(MAKE) -C src/cbor test-snapshot
else
cbor-test-snapshot: cbor-verify
endif

.PHONY: cbor-test-snapshot

# This rule is incompatible with `cbor` and `cbor-test-snapshot`
ifeq (,$(NO_PULSE))
cbor-snapshot: cbor-extract-krml
	+$(MAKE) -C src/cbor snapshot
else
cbor-snapshot:
endif

.PHONY: cbor-snapshot

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

.PHONY: cbor-det-c-test cbor-det-rust-test cbor-test cddl

ifeq (,$(NO_PULSE))
cddl-unit-tests: cddl
	+$(MAKE) -C src/cddl test
else
cddl-unit-tests:
endif

.PHONY: cddl-unit-tests

ifeq (,$(NO_PULSE))
cose-extract-krml: cddl
	+$(MAKE) -C src/cose extract-krml

cose-extract-test: cose-extract-krml
	+$(MAKE) -C src/cose test-extract

# This rule is incompatible with cose-extract-test
cose-snapshot: cose-extract-krml
	+$(MAKE) -C src/cose snapshot
else
cose-extract-krml:
cose-extract-test:
cose-snapshot:
endif

.PHONY: cose-extract-krml cose-extract-test cose-snapshot

cose-test: cose-extract-test cose-extracted-test

.PHONY: cose-test

cddl-test: cddl cddl-unit-tests

.PHONY: cddl-test

# cbor needed because we regenerate its Rust documentation
3d-doc-ci: 3d-doc-test cbor
	+$(MAKE) -C doc 3d-ci

.PHONY: 3d-doc-ci

3d-doc-snapshot: 3d $(NEED_Z3_TESTGEN)
	+$(MAKE) -C doc 3d-snapshot

.PHONY: 3d-doc-snapshot

clean-asn1:
	+$(MAKE) -C src/ASN1 clean

.PHONY: clean-asn1

clean-3d:
	+$(MAKE) -C src/3d clean

clean-lowparse:
	+$(MAKE) -C src/lowparse clean

clean-quackyducky:
	+$(MAKE) -C src/qd clean

clean-cbor-verify:
	+$(MAKE) -C src/cbor clean-verify

clean-cddl:
	+$(MAKE) -C src/cddl clean

.PHONY: clean-cbor-verify

clean-bin:
	rm -rf bin lib

.PHONY: clean-bin

clean-cose-test:
	+$(MAKE) -C src/cose clean-extract

.PHONY: clean-cose-test

clean-tests:
	+$(MAKE) -C tests clean

.PHONY: clean-tests

clean-3d-tests:
	+$(MAKE) -C src/3d/tests clean

.PHONY: clean-3d-tests

clean-doc:
	+$(MAKE) -C doc clean

.PHONY: clean-doc

clean: $(clean_rules)

.PHONY: all gen verify test gen-test clean quackyducky lowparse lowparse-test lowparse-fstar-test package 3d 3d-test lowparse-unit-test lowparse-bitfields-test release everparse 3d-unit-test 3d-doc-test ci clean-3d clean-lowparse clean-quackyducky asn1 asn1-test

release package package-noversion nuget-noversion everparse:
	+$(MAKE) -f package.Makefile $@

# For F* testing purposes, cf. FStarLang/FStar@fc30456a163c749843c50ee5f86fa22de7f8ad7a

lowparse-fstar-test:
	+$(MAKE) -C src/lowparse fstar-test
