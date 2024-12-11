all: snapshot

interface: spec.do pulse.do

snapshot: pulse/det/krml.do
	+$(MAKE) -C pulse/det $@

test-snapshot: pulse/det/krml.do
	+$(MAKE) -C pulse/det $@

spec.do:

spec/raw.do: spec.do

spec/raw/everparse.do: spec/raw.do

pulse.do: spec.do

pulse/raw.do: spec/raw.do pulse.do

pulse/raw/everparse.do: pulse/raw.do spec/raw/everparse.do

pulse/det/krml.do: pulse/raw/everparse.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all %.do

.PHONY: interface snapshot test-snapshot
