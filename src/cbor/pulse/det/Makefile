all: c.do rust.do

c.do:
	+$(MAKE) -C $(basename $@)

rust.do:
	cd rust && cargo build && cargo doc --no-deps

.PHONY: %.do

snapshot: rust-snapshot c.snapshot

.PHONY: rust-snapshot

rust-snapshot: rust.snapshot

local_curdir := $(CURDIR)
ifeq ($(OS),Windows_NT)
  local_curdir := $(shell cygpath -m $(local_curdir))
endif

# Custard writes into a `custard' subdirectory of the extraction directory, so
# under CUSTARD=1 the snapshot source is one level deeper and target_dir --
# which snapshot.Makefile resolves relative to the source -- needs one more
# `../' to compensate.
custard_up = $(if $(filter 1,$(CUSTARD)),../)

c.snapshot: source_dir=c/extracted$(if $(filter 1,$(CUSTARD)),/custard)
c.snapshot: target_dir=$(custard_up)..

rust.snapshot: source_dir=rust-extracted$(if $(filter 1,$(CUSTARD)),/custard)
rust.snapshot: target_dir=$(custard_up)../rust/src

snapshot: c.snapshot rust.snapshot

%.snapshot:
	+$(MAKE) -C $(source_dir) -f $(local_curdir)/snapshot.Makefile target_dir=$(target_dir) $(subst .,,$(suffix $@))
	+$(MAKE) $(basename $@).do

.PHONY: %.snapshot snapshot

c.test-snapshot: source_dir=c/extracted$(if $(filter 1,$(CUSTARD)),/custard)
c.test-snapshot: target_dir=$(custard_up)..

rust.test-snapshot: source_dir=rust-extracted$(if $(filter 1,$(CUSTARD)),/custard)
rust.test-snapshot: target_dir=$(custard_up)../rust/src

test-snapshot: rust.test-snapshot c.test-snapshot

%.test-snapshot:
	+$(MAKE) -C $(source_dir) -f $(local_curdir)/snapshot.Makefile target_dir=$(target_dir) $(subst .,,$(suffix $@))

.PHONY: %.test-snapshot test-snapshot

clean_dirs = $(addsuffix .clean,c vertest/c vertest/common)

$(clean_dirs): %.clean:
	+$(MAKE) -C $(basename $@) clean

rust.clean:
	cd $(basename $@) && cargo clean

rust-extracted.clean:
	rm -rf $(basename $@)

.PHONY: %.clean

clean: $(clean_dirs) rust.clean rust-extracted.clean
