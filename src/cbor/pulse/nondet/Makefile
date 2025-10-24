all: c.do

c.do:
	+$(MAKE) -C $(basename $@)

.PHONY: %.do

snapshot: c.snapshot

local_curdir := $(CURDIR)
ifeq ($(OS),Windows_NT)
  local_curdir := $(shell cygpath -m $(local_curdir))
endif

c.snapshot: source_dir=c-extracted
c.snapshot: target_dir=../c

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

rust-extracted.clean:
	rm -rf $(basename $@)

.PHONY: %.clean

clean: c-extracted.clean rust-extracted.clean c.clean

.PHONY: clean
