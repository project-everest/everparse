all: build

EVERPARSE_SRC_PATH = $(realpath ..)

build-c:
	+$(MAKE) -C c

.PHONY: build-c

build-rust:
	cd rust && cargo build

.PHONY: build-rust

build: build-c build-rust

.PHONY: build

.PHONY: all

test-extract-c:
	+$(MAKE) -C verifiedinterop test

test-extract-rust:
	+$(MAKE) -C generate-rust test

.PHONY: test-extract-c test-extract-rust

.PHONY: test-interop
test-interop: build-c
	+$(MAKE) -C interop

test-rust: build-rust
	cd rust && cargo test

.PHONY: test-rust

test-extracted: test-interop test-rust

.PHONY: test-extracted

test-extract: test-extract-c test-extract-rust

test: test-extract test-extracted

.PHONY: test-extract test

# This rule is incompatible with `test-extract`
snapshot: snapshot-c snapshot-rust

.PHONY: snapshot

snapshot-c:
	+$(MAKE) -C verifiedinterop snapshot
	+$(MAKE) build-c

.PHONY: snapshot-c

snapshot-rust:
	+$(MAKE) -C generate-rust snapshot
	+$(MAKE) build-rust

.PHONY: snapshot-c

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
