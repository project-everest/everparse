all-nofstar: cbor cose

clean_rules += clean-cbor clean-cose

.PHONY: all-nofstar

cbor:
	+$(MAKE) -C src/cbor/pulse/det

.PHONY: cbor

cose: cbor
	+$(MAKE) -C src/cose

.PHONY: cose

cbor-det-c-test: cbor
	+$(MAKE) -C src/cbor/pulse/det/c all-tests

.PHONY: cbor-det-c-test

# NOTE: I wish we could use `cargo -C ...` but see https://github.com/rust-lang/cargo/pull/11960
cbor-det-rust-test: cbor
	+cd src/cbor/pulse/det/rust && cargo test

.PHONY: cbor-det-rust-test

cbor-test-unverified: cbor-det-c-test cbor-det-rust-test

.PHONY: cbor-test-unverified

cose-extracted-test: cose
	+$(MAKE) -C src/cose test-extracted

.PHONY: cose-extracted-test

test-nofstar: all-nofstar cbor-test-unverified cose-extracted-test

.PHONY: test-nofstar

clean-cbor:
	+$(MAKE) -C src/cbor clean

.PHONY: clean-cbor

clean-cose:
	+$(MAKE) -C src/cose clean

.PHONY: clean-cose

clean: $(clean_rules)

.PHONY: clean
