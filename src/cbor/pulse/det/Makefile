all: c.do rust.do

c.do:
	+$(MAKE) -C $(basename $@)

rust.do:
	cd rust && cargo build && cargo doc --no-deps

krml.do:
	+$(MAKE) -C $(basename $@)

.PHONY: %.do

snapshot: rust-snapshot c.snapshot

.PHONY: rust-snapshot

rust-snapshot: rust.snapshot

local_curdir := $(CURDIR)
ifeq ($(OS),Windows_NT)
  local_curdir := $(shell cygpath -m $(local_curdir))
endif

c.snapshot: source_dir=c/extracted
c.snapshot: target_dir=..

rust.snapshot: source_dir=krml/rust-extracted
rust.snapshot: target_dir=../../rust/src

snapshot: c.snapshot rust.snapshot

%.snapshot:
	+$(MAKE) -C $(source_dir) -f $(local_curdir)/snapshot.Makefile target_dir=$(target_dir) $(subst .,,$(suffix $@))
	+$(MAKE) $(basename $@).do

.PHONY: %.snapshot snapshot

c.test-snapshot: source_dir=c/extracted
c.test-snapshot: target_dir=..

rust.test-snapshot: source_dir=krml/rust-extracted
rust.test-snapshot: target_dir=../../rust/src

test-snapshot: rust.test-snapshot c.test-snapshot

%.test-snapshot:
	+$(MAKE) -C $(source_dir) -f $(local_curdir)/snapshot.Makefile target_dir=$(target_dir) $(subst .,,$(suffix $@))

.PHONY: %.test-snapshot test-snapshot
