# ASN.1 DER differential tests: ours vs asn1tools vs rasn vs asn1-rs.
# See README.md. Run from src/ASN1 via `make test` (target difftest).
#
#   make check        run ours on every vector, and the other enabled
#                     implementations only on the vectors not in
#                     triage/known.json for them, then gate (default)
#   make check-all    run every enabled implementation on every vector,
#                     then gate, including the triage/known.json entries
#   make rebaseline   rewrite triage/known.json from check-all's results
#   make clean        remove out/, .venv/ and the Rust target/
#
# Opt-outs: ASN1_DIFFTEST_PY=0 skips asn1tools (no Python venv);
# ASN1_DIFFTEST_RUST=0 skips rasn and asn1-rs. ASN1_DIFFTEST_RUST defaults
# to 1 if a recent enough `cargo` is on PATH, 0 (with a warning) otherwise.

ifeq ($(OS),Windows_NT)
  local_curdir := $(shell cygpath -m $(CURDIR))
else
  local_curdir := $(CURDIR)
endif

OURS ?= $(local_curdir)/../evaluation/ASN1_Parser.exe
OUT := $(local_curdir)/out
MANIFEST := $(OUT)/manifest.json
REPORT := $(OUT)/report.md
SCHEMAS := $(local_curdir)/schemas
VECTORS := $(wildcard vectors/*.json)

PYTHON ?= python3
VENV_DIR := $(local_curdir)/.venv
ifeq ($(OS),Windows_NT)
VENV_PYTHON := $(VENV_DIR)/Scripts/python.exe
else
VENV_PYTHON := $(VENV_DIR)/bin/python
endif
ASN1_DIFFTEST_PY ?= 1

# The crates pinned in harness/rust/Cargo.lock need Rust >= 1.$(RUST_MIN_MINOR)
CARGO ?= cargo
RUST_MIN_MINOR := 89
ifeq (,$(ASN1_DIFFTEST_RUST))
cargo_minor := $(shell $(CARGO) --version 2>/dev/null | sed -n 's/^cargo 1\.\([0-9]*\).*/\1/p')
ifeq (,$(cargo_minor))
ASN1_DIFFTEST_RUST := 0
$(warning difftest: $(CARGO) not found, skipping the rasn and asn1-rs runners)
else ifeq (,$(shell test $(cargo_minor) -ge $(RUST_MIN_MINOR) && echo ok))
ASN1_DIFFTEST_RUST := 0
$(warning difftest: $(CARGO) is 1.$(cargo_minor) < 1.$(RUST_MIN_MINOR), skipping the rasn and asn1-rs runners)
else
ASN1_DIFFTEST_RUST := 1
endif
endif
RUST_DIR := $(local_curdir)/harness/rust
RUST_BIN := $(RUST_DIR)/target/release

# check-all writes every result to $(OUT); check writes the results of the
# other implementations, on their filtered manifests, to $(NEW).
NEW := $(OUT)/new
KNOWN := triage/known.json
OTHERS :=
ifeq (1,$(ASN1_DIFFTEST_PY))
OTHERS += asn1tools
endif
ifeq (1,$(ASN1_DIFFTEST_RUST))
OTHERS += rasn asn1-rs
endif
DISABLED := $(filter-out $(OTHERS),asn1tools rasn asn1-rs)
RESULTS := $(OUT)/ours.jsonl $(OTHERS:%=$(OUT)/%.jsonl)
NEW_RESULTS := $(OUT)/ours.jsonl $(OTHERS:%=$(NEW)/%.jsonl)

REPORT_ARGS = --manifest $(MANIFEST) --capabilities capabilities \
  --known $(KNOWN) --results $(OUT)
NEW_REPORT_ARGS = --manifest $(MANIFEST) --capabilities capabilities \
  --known $(KNOWN) --results $(NEW) --ours-results $(OUT) --new-only

all: check

GEN := $(OUT)/gen

$(MANIFEST): $(VECTORS) features.json report.py gen/mutate.py
	mkdir -p $(GEN)
	$(PYTHON) gen/mutate.py vectors $(GEN)/mutations.json
	$(PYTHON) report.py manifest vectors features.json $@ --gen $(GEN)

$(OUT)/ours.jsonl: $(MANIFEST) $(OURS)
	$(OURS) DIFFTEST $(MANIFEST) $@

# The stamp is only written once the pinned requirements are installed
# (the venv python itself may be a symlink to the system interpreter).
VENV_STAMP := $(VENV_DIR)/.installed
$(VENV_STAMP): harness/asn1tools/requirements.txt
	rm -rf $(VENV_DIR)
	$(PYTHON) -m venv $(VENV_DIR)
	$(VENV_PYTHON) -m pip install --quiet --disable-pip-version-check -r $<
	touch $@

venv: $(VENV_STAMP)

$(OUT)/asn1tools.jsonl: $(MANIFEST) $(VENV_STAMP) harness/asn1tools/runner.py $(wildcard schemas/*.asn)
	$(VENV_PYTHON) harness/asn1tools/runner.py $(SCHEMAS) $(MANIFEST) $@

$(NEW)/manifest.%.json: $(MANIFEST) $(KNOWN) report.py
	mkdir -p $(NEW)
	$(PYTHON) report.py filter --manifest $(MANIFEST) --known $(KNOWN) --impl $* $@

$(NEW)/asn1tools.jsonl: $(NEW)/manifest.asn1tools.json $(VENV_STAMP) harness/asn1tools/runner.py $(wildcard schemas/*.asn)
	$(VENV_PYTHON) harness/asn1tools/runner.py $(SCHEMAS) $< $@

# cargo does its own dependency tracking, so always ask it.
build-rust:
	cd $(RUST_DIR) && $(CARGO) build --release --locked --quiet

$(OUT)/rasn.jsonl: $(MANIFEST) build-rust
	$(RUST_BIN)/rasn-runner $(MANIFEST) $@

$(OUT)/asn1-rs.jsonl: $(MANIFEST) build-rust
	$(RUST_BIN)/asn1rs-runner $(MANIFEST) $@

$(NEW)/rasn.jsonl: $(NEW)/manifest.rasn.json build-rust
	$(RUST_BIN)/rasn-runner $< $@

$(NEW)/asn1-rs.jsonl: $(NEW)/manifest.asn1-rs.json build-rust
	$(RUST_BIN)/asn1rs-runner $< $@

# Results of disabled implementations are removed, so that they are not gated.
run: $(RESULTS)
	rm -f $(DISABLED:%=$(OUT)/%.jsonl)

run-new: $(NEW_RESULTS)
	rm -f $(DISABLED:%=$(NEW)/%.jsonl)

check: run-new
	$(PYTHON) report.py check $(NEW_REPORT_ARGS) --report $(REPORT)

check-all: run
	$(PYTHON) report.py check $(REPORT_ARGS) --report $(REPORT)

rebaseline: run
	$(PYTHON) report.py rebaseline $(REPORT_ARGS)

clean:
	rm -rf $(OUT) $(VENV_DIR)
	-cd $(RUST_DIR) && $(CARGO) clean

.PHONY: all venv build-rust run run-new check check-all rebaseline clean
