all: extract

extract-krml-c:
	+$(MAKE) -f c.Makefile extract-krml

.PHONY: extract-krml-c

extract-krml-rust:
	+$(MAKE) -f rust.Makefile extract-krml

.PHONY: extract-krml-rust

# The slice-typed byte fields of CBOR.Pulse.Raw.Type extract differently per backend
# (see CBOR.Pulse.Raw.Slice), so C and Rust are extracted in two passes, each
# selecting the matching slice-* implementation via CBOR_SLICE_BACKEND and writing to
# its own extracted-$(CBOR_SLICE_BACKEND) directory.
extract-krml: extract-krml-c extract-krml-rust

.PHONY: extract-krml

extract-c: extract-krml-c
	+$(MAKE) -f c.Makefile extract

.PHONY: extract-c

extract-rust: extract-krml-rust
	+$(MAKE) -f rust.Makefile extract

.PHONY: extract-rust

extract: extract-c extract-rust

.PHONY: extract

clean:
	rm -rf extracted extracted-c extracted-rust

.PHONY: clean
