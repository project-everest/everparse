all: extract

# Each (slice backend, API) pair is its own whole-program extraction: the
# deterministic and non-deterministic APIs are separate programs, and under
# whole-program extraction there is no way to drop one from the other's output
# after the fact, the way filtering the per-module .krml files used to.
extract-krml-c:
	+$(MAKE) -f c.Makefile extract-krml CBOR_API=det
	+$(MAKE) -f c.Makefile extract-krml CBOR_API=nondet

.PHONY: extract-krml-c

extract-krml-rust:
	+$(MAKE) -f rust.Makefile extract-krml CBOR_API=det
	+$(MAKE) -f rust.Makefile extract-krml CBOR_API=nondet

.PHONY: extract-krml-rust

# The slice-typed byte fields of CBOR.Pulse.Raw.Type extract differently per backend
# (see CBOR.Pulse.Raw.Slice), so C and Rust are extracted in two passes, each
# selecting the matching slice-* implementation via CBOR_SLICE_BACKEND and writing to
# its own extracted-$(CBOR_SLICE_BACKEND) directory.
extract-krml: extract-krml-c extract-krml-rust

.PHONY: extract-krml

extract-c: extract-krml-c
	+$(MAKE) -f c.Makefile extract CBOR_API=det
	+$(MAKE) -f c.Makefile extract CBOR_API=nondet

.PHONY: extract-c

extract-rust: extract-krml-rust
	+$(MAKE) -f rust.Makefile extract CBOR_API=det
	+$(MAKE) -f rust.Makefile extract CBOR_API=nondet

.PHONY: extract-rust

extract: extract-c extract-rust

.PHONY: extract

clean:
	rm -rf extracted extracted-c-det extracted-c-nondet extracted-rust-det extracted-rust-nondet h-extracted

.PHONY: clean
