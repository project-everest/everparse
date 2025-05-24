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

.venv:
	rm -rf $@ $@.tmp
	python3 -m venv $@.tmp
	$@.tmp/bin/python3 -m pip install pycose
	mv $@.tmp $@

.PHONY: test-interop
test-interop: build-c .venv
	+$(MAKE) -C interop

.PHONY: test-verified-interop
test-verified-interop: build-c .venv
	+$(MAKE) -C verifiedinterop/test

test-rust: build-rust
	cd rust && cargo test

.PHONY: test-rust

test-extracted: test-interop test-verified-interop test-rust

.PHONY: test-extracted

test-batch-c: cose.cddl
	rm -rf $@ $@.tmp
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe --odir $@.tmp --tmpdir $@.tmp $< $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl --mname COSEBatchTest --admit
	mv $@.tmp $@

test-batch-rust: cose.cddl
	rm -rf $@ $@.tmp
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe --odir $@.tmp --tmpdir $@.tmp $< $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl --mname COSEBatchTest --rust --admit
	mv $@.tmp $@

test-extract: test-extract-c test-extract-rust test-batch-c test-batch-rust

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
