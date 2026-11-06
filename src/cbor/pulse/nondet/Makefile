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

local_everparse_home := $(realpath ../../../..)
ifeq ($(OS),Windows_NT)
  local_everparse_home := $(shell cygpath -m $(local_everparse_home))
endif

# The public C headers are snapshotted into the shared include directory
# rather than next to the C sources (see snapshot.Makefile).
header_dir := $(local_everparse_home)/include/everparse

# The extracted headers that are part of the public API; any other extracted
# header stays next to the C sources (see snapshot.Makefile.) Hand-written
# public headers (e.g. CBORNondetHashRandom.h) live in include/everparse
# directly; the list of installed headers is in install.Makefile.
c.snapshot c.test-snapshot: PUBLIC_HEADERS := CBORNondet.h CBORNondetType.h

%.snapshot:
	+$(MAKE) -C $(source_dir) -f $(local_curdir)/snapshot.Makefile target_dir=$(target_dir) header_dir=$(header_dir) PUBLIC_HEADERS='$(PUBLIC_HEADERS)' $(subst .,,$(suffix $@))
	+$(MAKE) $(basename $@).do

.PHONY: %.snapshot snapshot

c.test-snapshot: source_dir=c-extracted
c.test-snapshot: target_dir=../c

test-snapshot: c.test-snapshot

%.test-snapshot:
	+$(MAKE) -C $(source_dir) -f $(local_curdir)/snapshot.Makefile target_dir=$(target_dir) header_dir=$(header_dir) PUBLIC_HEADERS='$(PUBLIC_HEADERS)' $(subst .,,$(suffix $@))

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
