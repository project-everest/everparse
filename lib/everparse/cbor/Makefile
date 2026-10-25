all: snapshot

EVERPARSE_HOME := $(realpath ../../..)

# The C and Rust snapshots, and the KaRaMeL extraction that produces them, are
# build products of this library rather than parts of it, so they stay under
# src/cbor/pulse while the F* sources live here.
CBOR_EXTRACT_PATH := $(EVERPARSE_HOME)/src/cbor/pulse

interface: spec.do pulse.do

snapshot: det/snapshot nondet/snapshot

.PHONY: det/snapshot nondet/snapshot

det/snapshot: extract
	+$(MAKE) -C $(CBOR_EXTRACT_PATH)/det snapshot

nondet/snapshot: extract
	+$(MAKE) -C $(CBOR_EXTRACT_PATH)/nondet snapshot

test-snapshot: det/test-snapshot nondet/test-snapshot

.PHONY: det/test-snapshot nondet/test-snapshot

det/test-snapshot: extract
	+$(MAKE) -C $(CBOR_EXTRACT_PATH)/det test-snapshot

nondet/test-snapshot: extract
	+$(MAKE) -C $(CBOR_EXTRACT_PATH)/nondet test-snapshot

# Build the two CBOR.Pulse.Raw.Slice backend implementations (each verified by its
# own Makefile under pulse/raw/slice-{c,rust}) before invoking krml: the krml passes
# treat the slice as already cached (ALREADY_CACHED='*,-CBOR,CBOR.Pulse.Raw.Slice,',
# matching the krml Makefile), so krml's dependency scan requires the slice .checked
# to already exist. On separate recipe lines, hence sequential, so the two backend
# builds never race on the shared CBOR.Pulse.Raw.Slice.fsti.checked.
slice-c:
	+$(MAKE) -C pulse/raw/slice-c

slice-rust:
	+$(MAKE) -C pulse/raw/slice-rust

.PHONY: slice-c slice-rust

extract-krml: slice-c slice-rust
	+$(MAKE) -C $(CBOR_EXTRACT_PATH)/krml extract-krml

.PHONY: extract-krml

extract: extract-krml
	+$(MAKE) -C $(CBOR_EXTRACT_PATH)/krml

.PHONY: extract

spec.do:

spec/raw.do: spec.do

spec/raw/everparse.do: spec/raw.do

pulse.do: spec.do

pulse/raw.do: spec/raw.do pulse.do

pulse/raw/everparse.do: pulse/raw.do spec/raw/everparse.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all %.do

.PHONY: interface snapshot test-snapshot

clean:
	+$(MAKE) -C $(CBOR_EXTRACT_PATH)/det clean
	+$(MAKE) -C $(CBOR_EXTRACT_PATH)/nondet clean

.PHONY: clean

clean-verify: spec.clean spec/raw.clean spec/raw/everparse.clean pulse.clean pulse/raw.clean pulse/raw/everparse.clean

clean-verify: pulse/raw/slice-c.clean pulse/raw/slice-rust.clean

clean-verify:
	+$(MAKE) -C $(CBOR_EXTRACT_PATH)/krml clean

.PHONY: clean-verify

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
