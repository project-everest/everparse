files=$(shell find . -type f)

%.snapshot:
	cp $(basename $@) $(target_dir)/$(basename $@)

snapshot: $(addsuffix .snapshot,$(files))

.PHONY: snapshot %.snapshot

ifeq ($(EVERPARSE_CHECK_DIFF),1) # Set this variable to enable diffs
test-snapshot: $(addsuffix .test-snapshot,$(files))
else
test-snapshot:
endif

%.test-snapshot:
	diff $(basename $@) $(target_dir)/$(basename $@)

.PHONY: test-snapshot %.test-snapshot
