all: snapshot encrypt

encrypt: cose-encrypt.cddl ../cddl/spec/postlude.cddl
	rm -rf $@.tmp $@
	$(EVERPARSE_SRC_PATH)/../bin/cddl.exe $^ --odir $@.tmp
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

.venv:
	rm -rf $@ $@.tmp
	python3 -m venv $@.tmp
	$@.tmp/bin/python3 -m pip install -r python-requirements.txt
	mv $@.tmp $@

.PHONY: test-interop
test-interop: snapshot-c .venv
	+$(MAKE) -C interop

.PHONY: test-verified-interop
test-verified-interop: snapshot-c .venv
	+$(MAKE) -C verifiedinterop/test

test-rust: snapshot-rust
	cd rust && cargo test

.PHONY: test-rust

test-extracted: test-interop test-verified-interop test-rust

.PHONY: test-extracted

test: test-extracted

.PHONY: test

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
