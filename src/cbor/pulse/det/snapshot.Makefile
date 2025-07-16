files=$(shell find . -type f)

%.snapshot:
	cp $(basename $@) $(target_dir)/$(basename $@)

snapshot: $(addsuffix .snapshot,$(files))

.PHONY: snapshot %.snapshot

test-snapshot: $(addsuffix .test-snapshot,$(files))

%.test-snapshot:
	diff $(basename $@) $(target_dir)/$(basename $@)

.PHONY: test-snapshot %.test-snapshot
