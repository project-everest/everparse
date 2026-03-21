all: c.do rust.do

c.do:
	+$(MAKE) -C $(basename $@)

rust.do:
	cd rust && cargo build && cargo doc --no-deps

.PHONY: %.do

snapshot: c.snapshot rust.snapshot

local_curdir := $(CURDIR)
ifeq ($(OS),Windows_NT)
  local_curdir := $(shell cygpath -m $(local_curdir))
endif

c.snapshot: source_dir=c-extracted
c.snapshot: target_dir=../c

rust.snapshot: source_dir=rust-extracted
rust.snapshot: target_dir=../rust/src

%.snapshot:
	+$(MAKE) -C $(source_dir) -f $(local_curdir)/snapshot.Makefile target_dir=$(target_dir) $(subst .,,$(suffix $@))
	+$(MAKE) $(basename $@).do

.PHONY: %.snapshot snapshot

c.test-snapshot: source_dir=c-extracted
c.test-snapshot: target_dir=../c

test-snapshot: c.test-snapshot

%.test-snapshot:
	+$(MAKE) -C $(source_dir) -f $(local_curdir)/snapshot.Makefile target_dir=$(target_dir) $(subst .,,$(suffix $@))

.PHONY: %.test-snapshot test-snapshot

clean_dirs = $(addsuffix .clean,c)

$(clean_dirs): %.clean:
	+$(MAKE) -C $(basename $@) clean

c-extracted.clean:
	rm -rf $(basename $@)

rust.clean:
	cd $(basename $@) && cargo clean

rust-extracted.clean:
	rm -rf $(basename $@)

.PHONY: %.clean

clean: c-extracted.clean rust-extracted.clean c.clean

clean: rust.clean

.PHONY: clean
