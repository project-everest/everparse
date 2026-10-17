files := $(shell find . -type f)

# Headers at the top level of the extraction directory are the public API of
# the library: they are snapshotted into $(header_dir), the shared EverParse
# include directory, rather than alongside the sources. Headers in
# subdirectories (internal/) stay with the sources. Passes that extract no
# public header at all (Rust) just leave $(header_dir) unused.
public_headers := $(shell find . -maxdepth 1 -type f -name '*.h')
other_files := $(filter-out $(public_headers),$(files))

header_dir ?= $(target_dir)

# KaRaMeL refers to the public headers from the internal/ subdirectory as
# "../CBORDet.h", which no longer resolves. Rewrite those as we snapshot into
# <everparse/CBORDet.h>, found relative to the parent of $(header_dir): a
# quoted "CBORDet.h" would resolve to internal/CBORDet.h itself, and an
# unqualified <CBORDet.h> could pick up an unrelated header of that name.
header_fixup := -e '' $(foreach h,$(notdir $(public_headers)),-e 's|^#include "\.\./$(h)"|#include <everparse/$(h)>|')

%.snapshot:
	sed $(header_fixup) $(basename $@) > $(target_dir)/$(basename $@)

%.snapshot-header:
	mkdir -p $(header_dir)
	cp $(basename $@) $(header_dir)/$(notdir $(basename $@))

snapshot: $(addsuffix .snapshot,$(other_files)) $(addsuffix .snapshot-header,$(public_headers))

.PHONY: snapshot %.snapshot %.snapshot-header

ifeq ($(EVERPARSE_CHECK_DIFF),1) # Set this variable to enable diffs
test-snapshot: $(addsuffix .test-snapshot,$(other_files)) $(addsuffix .test-snapshot-header,$(public_headers))
else
test-snapshot:
endif

%.test-snapshot:
	sed $(header_fixup) $(basename $@) | diff - $(target_dir)/$(basename $@)

%.test-snapshot-header:
	diff $(basename $@) $(header_dir)/$(notdir $(basename $@))

.PHONY: test-snapshot %.test-snapshot %.test-snapshot-header
