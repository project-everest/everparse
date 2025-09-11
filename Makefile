#NOTE: if you want to add global F* options, you need to do the following:
# 1. Add them to FSTAR_OPTIONS in src/fstar.Makefile
# 2. Add them to fstar_args0 in src/3d/ocaml/Batch.ml

all: package-subset asn1 cbor

.PHONY: all

# Include specific options on release branches (e.g. EVERPARSE_OPAM_REPOSITORY)
-include release.Makefile

package-subset: quackyducky lowparse 3d

ifeq (,$(OS))
export OS := $(shell uname)
endif
ifneq ($(OS),Windows_NT)
package-subset: cddl
endif
ifneq ($(OS),Darwin)
all: cose
endif

.PHONY: package-subset

include nofstar.Makefile

export EVERPARSE_OPT_PATH := $(realpath opt)
ifeq ($(OS),Windows_NT)
export EVERPARSE_OPT_PATH := $(shell cygpath -m $(EVERPARSE_OPT_PATH))
# Pulse does not compile on Windows
NO_PULSE := 1
endif

ifeq (,$(NO_PULSE))
all: cddl cbor-interface
endif

$(EVERPARSE_OPT_PATH)/everest:
	+$(MAKE) -C $(dir $@) -f git-clone.Makefile $(notdir $@)

ifeq (,$(OPAMNODEPEXTS))
export OPAMNODEPEXTS := 1
endif
ifeq (,$(OPAMYES))
export OPAMYES := 1
endif

cygwin_local_install :=
ifeq ($(OS),Windows_NT)
cygwin_local_install += --cygwin-local-install
endif

$(EVERPARSE_OPT_PATH)/opam: $(EVERPARSE_OPT_PATH)/everest
	rm -rf $@ $@.tmp
	if ! { opam init $(cygwin_local_install) --no-setup --root=$(EVERPARSE_OPT_PATH)/opam --compiler=5.3.0 $(EVERPARSE_OPAM_REPOSITORY) && eval "$$(opam env --root=$(EVERPARSE_OPT_PATH)/opam --set-root)" && bash $(EVERPARSE_OPT_PATH)/everest/everest opam ; } ; then mv $@ $@.tmp ; exit 1 ; fi
	touch $@

NEED_OPAM :=
ifeq (,$(EVERPARSE_USE_OPAMROOT))
NEED_OPAM := $(EVERPARSE_OPT_PATH)/opam
with_opam := eval "$$(opam env --root="$(EVERPARSE_OPT_PATH)/opam" --set-root)" &&
endif

Z3_VERSION := 4.13.3

NEED_FSTAR :=
ifeq (,$(FSTAR_EXE))
export FSTAR_EXE := $(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe
NEED_FSTAR := $(FSTAR_EXE)
z3_exe := $(shell $(FSTAR_EXE) --locate_z3 \$(Z3_VERSION) 2>/dev/null)
else
# F* already exists, so we assume its fstar-lib is already compiled
NEED_OPAM :=
endif

NEED_KRML :=
ifeq (,$(KRML_HOME))
export KRML_HOME := $(EVERPARSE_OPT_PATH)/karamel
NEED_KRML := $(KRML_HOME)/_build/default/src/Karamel.exe
else
ifneq (,$(NEED_FSTAR))
$(error "Inconsistent setup: KRML_HOME set but FSTAR_EXE not set")
endif
endif

NEED_PULSE :=
ifeq (,$(NO_PULSE))
ifeq (,$(PULSE_HOME))
export PULSE_HOME := $(EVERPARSE_OPT_PATH)/pulse/out
NEED_PULSE := $(PULSE_HOME)
else
ifneq (,$(NEED_FSTAR))
$(error "Inconsistent setup: PULSE_HOME set but FSTAR_EXE not set")
endif
endif
endif

ifeq (,$(z3_exe))
z3_exe := $(shell which z3-$(Z3_VERSION))
ifneq (0,$(.SHELLSTATUS))
z3_exe :=
endif
endif
ifeq (,$(z3_exe))
NEED_Z3 := $(EVERPARSE_OPT_PATH)/z3
ifeq ($(OS),Windows_NT)
export PATH := $(shell cygpath -u $(NEED_Z3)):$(PATH)
else
export PATH := $(NEED_Z3):$(PATH)
endif
else
NEED_Z3 := 
endif
ifeq (1,$(ADMIT))
OTHERFLAGS += --admit_smt_queries true
export OTHERFLAGS
NEED_Z3 :=
endif

opam-env.Makefile: $(NEED_OPAM)
	rm -rf $@.tmp
	$(EVERPARSE_OPT_PATH)/opam-env.sh > $@.tmp
	echo >> $@.tmp
	echo env: opam-env >> $@.tmp
	echo .PHONY: opam-env >> $@.tmp
	echo opam-env: >> $@.tmp
	echo "	\"$(EVERPARSE_OPT_PATH)\"/opam-env.sh --shell" >> $@.tmp
	mv $@.tmp $@
	touch $@

include opam-env.Makefile

$(EVERPARSE_OPT_PATH)/FStar:
	+$(MAKE) -C $(dir $@) -f git-clone.Makefile $(notdir $@)

$(EVERPARSE_OPT_PATH)/FStar/out/bin/fstar.exe: $(EVERPARSE_OPT_PATH)/FStar $(NEED_OPAM)
	+$(with_opam) $(MAKE) -C $< ADMIT=1
	touch $@

$(EVERPARSE_OPT_PATH)/z3: $(EVERPARSE_OPT_PATH)/FStar
	rm -rf $@ $@.tmp
	mkdir -p $@.tmp
	$</.scripts/get_fstar_z3.sh $@.tmp
	rm -rf $@.tmp/z3-4.8.5
	mv $@.tmp $@
	touch $@

$(EVERPARSE_OPT_PATH)/karamel:
	+$(MAKE) -C $(dir $@) -f git-clone.Makefile $(notdir $@)

$(EVERPARSE_OPT_PATH)/karamel/_build/default/src/Karamel.exe: $(EVERPARSE_OPT_PATH)/karamel $(NEED_FSTAR) $(NEED_OPAM)
	+$(with_opam) env OTHERFLAGS='--admit_smt_queries true' $(MAKE) -C $<
	touch $@

$(EVERPARSE_OPT_PATH)/pulse:
	+$(MAKE) -C $(dir $@) -f git-clone.Makefile $(notdir $@)

$(EVERPARSE_OPT_PATH)/pulse/out: $(EVERPARSE_OPT_PATH)/pulse $(NEED_FSTAR) $(NEED_OPAM)
	+$(with_opam) $(MAKE) -C $< ADMIT=1
	touch $@

env:
	@echo export FSTAR_EXE=$(FSTAR_EXE)
	@echo export KRML_HOME=$(KRML_HOME)
ifeq (,$(NO_PULSE))
	@echo export PULSE_HOME=$(PULSE_HOME)
endif
ifeq ($(OS),Windows_NT)
	@echo export PATH=$(shell cygpath -u $(EVERPARSE_OPT_PATH))/FStar/bin:$(shell cygpath -u $(EVERPARSE_OPT_PATH))/z3:\"'$$PATH'\"
else
	@echo export PATH=$(EVERPARSE_OPT_PATH)/FStar/bin:$(EVERPARSE_OPT_PATH)/z3:\"'$$PATH'\"
endif

.PHONY: env

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

deps: $(NEED_OPAM) $(NEED_FSTAR) $(NEED_Z3) $(NEED_KRML) $(NEED_PULSE)

.PHONY: deps

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

quackyducky: bin/qd.exe lowparse

bin/qd.exe: $(NEED_OPAM)
	+$(MAKE) -C src/qd

.gen-test.touch: bin/qd.exe tests/unittests.rfc tests/bitcoin.rfc
	rm -f tests/unit/*.fst tests/unit/*.fsti
	bin/qd.exe -odir tests/unit tests/unittests.rfc
	bin/qd.exe -low -odir tests/unit tests/bitcoin.rfc
	touch $@

gen-test: .gen-test.touch

lowparse-unit-test: lowparse
	+$(MAKE) -C tests/lowparse

3d-unit-test: 3d
ifneq ($(OS),Darwin)
	+$(MAKE) -C src/3d test
endif

3d-doc-test: 3d
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

cddl: cbor-interface cddl-spec cddl-tool

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

cose-test: cose-extract-test cose-extracted-test

.PHONY: cose-test

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
