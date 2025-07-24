files=$(shell find . -type f)

%.snapshot:
	cp $(basename $@) $(target_dir)/$(basename $@)

snapshot: $(addsuffix .snapshot,$(files))

.PHONY: snapshot %.snapshot

ifeq ($(EVERPARSE_NO_DIFF),) # Set this variable to disable diffs
test-snapshot: $(addsuffix .test-snapshot,$(files))
endif

%.test-snapshot:
	diff $(basename $@) $(target_dir)/$(basename $@)

.PHONY: test-snapshot %.test-snapshot
