all: build

ifeq (1,$(ADMIT))
CDDL_ADMIT := --admit
else
CDDL_ADMIT :=
endif

encrypt: cose-encrypt.cddl ../cddl/spec/postlude.cddl
	rm -rf $@.tmp $@
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $@.tmp $(CDDL_ADMIT)
	mv $@.tmp $@

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

extract-krml: extract-krml-c extract-krml-rust

.PHONY: extract-krml

extract-krml-c:
	+$(MAKE) -C verifiedinterop extract-krml

.PHONY: extract-krml-c

extract-krml-rust:
	+$(MAKE) -C generate-rust extract-krml

.PHONY: extract-krml-rust

test-extract-c: extract-krml-c
	+$(MAKE) -C verifiedinterop test

test-extract-rust: extract-krml-rust
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

test-batch-c: cose-sign.cddl
	rm -rf $@ $@.tmp
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe --odir $@.tmp --tmpdir $@.tmp $< $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl --mname COSEBatchTest --admit
	mv $@.tmp $@

test-batch-rust: cose-sign.cddl
	rm -rf $@ $@.tmp
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe --odir $@.tmp --tmpdir $@.tmp $< $(EVERPARSE_SRC_PATH)/cddl/spec/postlude.cddl --mname COSEBatchTest --rust --admit
	mv $@.tmp $@

test-extract: test-extract-c test-extract-rust test-batch-c test-batch-rust encrypt

test: test-extract test-extracted

.PHONY: test-extract test

# This rule is incompatible with `test-extract`
snapshot: snapshot-c snapshot-rust

.PHONY: snapshot

snapshot-c: extract-krml-c
	+$(MAKE) -C verifiedinterop snapshot
	+$(MAKE) build-c

.PHONY: snapshot-c

snapshot-rust: extract-krml-rust
	+$(MAKE) -C generate-rust snapshot
	+$(MAKE) build-rust

.PHONY: snapshot-c

clean-c:
	+$(MAKE) -C c clean

.PHONY: clean-c

clean-test-verified-interop:
	+$(MAKE) -C verifiedinterop/test clean

.PHONY: clean-test-verified-interop

clean-test-interop:
	+$(MAKE) -C interop clean

.PHONY: clean-test-interop

clean-venv:
	rm -rf .venv

.PHONY: clean-venv

clean-rust:
	cd rust && cargo clean

.PHONY: clean-rust

clean: clean-c clean-rust clean-test-verified-interop clean-venv clean-test-interop clean-test-batch clean-encrypt

.PHONY: clean

clean-encrypt:
	rm -rf encrypt

.PHONY: clean-encrypt

clean-extract-c:
	+$(MAKE) -C verifiedinterop clean

.PHONY: clean-extract-c

clean-extract-rust:
	+$(MAKE) -C generate-rust clean

.PHONY: clean-extract-rust

clean-extract: clean-extract-c clean-extract-rust

.PHONY: clean-extract

clean-test-batch:
	rm -rf test-batch-c test-batch-rust

.PHONY: clean-test-batch

# Uncomment if you want to edit the produced F* file
# include extract.Makefile
