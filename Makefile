# NOTE: if you want to add global F* options, you need to do the following:
# 1. Add them to FSTAR_OPTIONS in src/fstar.Makefile

all: pulseparse cbor cddl cose

.PHONY: all

test: pulseparse-test cbor-test cddl-test cose-test

.PHONY: test

# Dependencies and Configuration

export EVERPARSE_OPT_PATH=$(realpath opt)
-include $(EVERPARSE_OPT_PATH)/opam-env.Makefile

export FSTAR_EXE ?= $(wildcard $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe)
export KRML_HOME ?= $(EVERPARSE_OPT_PATH)/karamel
export PULSE_HOME ?= $(EVERPARSE_OPT_PATH)/pulse/out
EVEREST_HOME ?= $(EVERPARSE_OPT_PATH)/everest
export PATH := $(EVERPARSE_OPT_PATH)/z3:$(PATH)

include $(EVERPARSE_OPT_PATH)/env.Makefile

$(EVERPARSE_OPT_PATH)/everest:
	+$(MAKE) -C $(EVERPARSE_OPT_PATH) everest

EVERPARSE_SRC_PATH = $(realpath src)

ALREADY_CACHED := *,-LowParse,-EverParse3d,-ASN1,-CBOR,-CDDL,

SRC_DIRS += src/lowparse src/cbor/spec src/cbor/spec/raw src/cbor/spec/raw/everparse src/cddl/spec

SRC_DIRS += src/lowparse/pulse src/cbor/pulse src/cbor/pulse/raw src/cbor/pulse/raw/everparse src/cddl/pulse src/cddl/tool

ifneq (,$(FSTAR_EXE))

include $(EVERPARSE_SRC_PATH)/karamel.Makefile
include $(EVERPARSE_SRC_PATH)/pulse.Makefile
include $(EVERPARSE_SRC_PATH)/common.Makefile

endif

# PulseParse

pulseparse_filter := src/lowparse/pulse/%

lowparse_files := $(filter-out $(pulseparse_filter),$(filter src/lowparse/%,$(ALL_CHECKED_FILES)))

pulseparse_files := $(filter $(pulseparse_filter),$(filter src/lowparse/%,$(ALL_CHECKED_FILES)))

# This is LowParse from Ramananandro et al.'s EverParse (USENIX Security 2019)
$(lowparse_files): FSTAR_OPTIONS += --admit_smt_queries true

lowparse: $(lowparse_files)

.PHONY: lowparse

pulseparse: $(pulseparse_files)

.PHONY: pulseparse

# PulseParse tests

pulseparse-test: pulseparse
	+$(MAKE) -C tests/pulse

.PHONY: pulseparse-test

# EverCBOR

cbor-verify: $(filter src/cbor/spec/% src/cbor/pulse/%,$(ALL_CHECKED_FILES))

.PHONY: cbor-verify

cbor-extract-pre: cbor-verify pulseparse

.PHONY: cbor-extract-pre

cbor: cbor-extract-pre
	+$(MAKE) -C src/cbor snapshot

.PHONY: cbor

# EverCBOR tests

cbor-det-c-test: cbor
	+$(MAKE) -C src/cbor/pulse/det/c all-tests

.PHONY: cbor-det-c-test

cbor-det-c-vertest: cbor
	+$(MAKE) -C src/cbor/pulse/det/vertest/c

.PHONY: cbor-det-c-vertest

cbor-det-common-vertest: cbor
	+$(MAKE) -C src/cbor/pulse/det/vertest/common

.PHONY: cbor-det-common-vertest

# NOTE: I wish we could use `cargo -C ...` but see https://github.com/rust-lang/cargo/pull/11960
cbor-det-rust-test: cbor
	+cd src/cbor/pulse/det/rust && cargo test

.PHONY: cbor-det-rust-test

cbor-test-unverified: cbor-det-c-test cbor-det-rust-test

.PHONY: cbor-test-unverified

cbor-test-verified: cbor-det-c-vertest cbor-det-common-vertest

.PHONY: cbor-test-verified

cbor-test: cbor-test-unverified cbor-test-verified

.PHONY: cbor-test

# EverCDDL

cddl-spec: $(filter src/cddl/spec/%,$(ALL_CHECKED_FILES))

.PHONY: cddl-spec

cddl-pulse: cddl-spec $(filter src/cddl/pulse/%,$(ALL_CHECKED_FILES))

.PHONY: cddl-pulse

cddl: cbor cddl-pulse $(filter src/cddl/tool/%,$(ALL_CHECKED_FILES))
	+$(MAKE) -C src/cddl/tool

.PHONY: cddl

# EverCDDL tests

cddl-unit-tests: cddl
	+$(MAKE) -C src/cddl/tests unit.do

.PHONY: cddl-unit-tests

cddl-dpe: cddl
	+$(MAKE) -C src/cddl/tests dpe.do

.PHONY: cddl-dpe

cddl-other-tests: cddl
	+$(MAKE) -C src/cddl/tests others

.PHONY: cddl-other-tests

cddl-test: cddl cddl-unit-tests cddl-dpe cddl-other-tests

.PHONY: cddl-test

# EverCOSE

cose: cddl
	+$(MAKE) -C src/cose

.PHONY: cose

# EverCOSE tests

cose-test: cose
	+$(MAKE) -C src/cose test

.PHONY: cose-test
