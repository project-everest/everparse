all-nofstar: cbor cose

clean_rules += clean-cbor clean-cose

.PHONY: all-nofstar

cbor: cbor-det cbor-nondet

cbor-det:
	+$(MAKE) -C src/cbor/pulse/det

cbor-nondet:
	+$(MAKE) -C src/cbor/pulse/nondet

.PHONY: cbor cbor-det cbor-nondet

cose: cbor
	+$(MAKE) -C src/cose

.PHONY: cose

cbor-det-c-test: cbor
	+$(MAKE) -C src/cbor/pulse/det/c all-tests

.PHONY: cbor-det-c-test

cbor-nondet-c-test: cbor
	+$(MAKE) -C src/cbor/pulse/nondet/c all-tests

.PHONY: cbor-nondet-c-test

# NOTE: I wish we could use `cargo -C ...` but see https://github.com/rust-lang/cargo/pull/11960
cbor-det-rust-test: cbor
	+cd src/cbor/pulse/det/rust && cargo test

.PHONY: cbor-det-rust-test

cbor-nondet-rust-test: cbor
	+cd src/cbor/pulse/nondet/rust && cargo test

.PHONY: cbor-nondet-rust-test

cbor-shared-test: cbor
	+$(MAKE) -C share/everparse/tests/cbor run

.PHONY: cbor-shared-test

# Re-validates the artefacts written by cbor-shared-test (in
# share/everparse/tests/cbor/out) through the Rust det and nondet APIs.
cbor-rust-shared-test: cbor-shared-test
	+cd src/cbor/tests_rust && CBOR_TEST_OUT_DIR=$(CURDIR)/share/everparse/tests/cbor/out cargo test --release

.PHONY: cbor-rust-shared-test

cbor-test-unverified: cbor-det-c-test cbor-det-rust-test cbor-nondet-c-test cbor-nondet-rust-test cbor-shared-test cbor-rust-shared-test

.PHONY: cbor-test-unverified

cose-extracted-test: cose
	+$(MAKE) -C src/cose test-extracted

.PHONY: cose-extracted-test

test-nofstar: all-nofstar cbor-test-unverified cose-extracted-test

.PHONY: test-nofstar

clean-cbor:
	+$(MAKE) -C lib/everparse/cbor clean
	+$(MAKE) -C share/everparse/tests/cbor clean
	rm -rf src/cbor/tests_rust/target src/cbor/tests_rust/Cargo.lock

.PHONY: clean-cbor

clean-cose:
	+$(MAKE) -C src/cose clean

.PHONY: clean-cose

clean: $(clean_rules)

.PHONY: clean
