all: snapshot

interface: spec.do pulse.do

snapshot: det/snapshot nondet/snapshot

.PHONY: det/snapshot nondet/snapshot

det/snapshot: extract
	+$(MAKE) -C pulse/$(dir $@) $(notdir $@)

nondet/snapshot: extract
	+$(MAKE) -C pulse/$(dir $@) $(notdir $@)

test-snapshot: det/test-snapshot nondet/test-snapshot

.PHONY: det/test-snapshot nondet/test-snapshot

det/test-snapshot: extract
	+$(MAKE) -C pulse/$(dir $@) $(notdir $@)

nondet/test-snapshot: extract
	+$(MAKE) -C pulse/$(dir $@) $(notdir $@)

extract-krml:
	+$(MAKE) -C pulse/krml extract-krml ALREADY_CACHED='*,-CBOR,'

.PHONY: extract-krml

extract: extract-krml
	+$(MAKE) -C pulse/krml ALREADY_CACHED='*,-CBOR,'

.PHONY: extract

spec.do:

spec/raw.do: spec.do

spec/raw/everparse.do: spec/raw.do

pulse.do: spec.do

pulse/raw.do: spec/raw.do pulse.do

pulse/raw/everparse.do: pulse/raw.do spec/raw/everparse.do

pulse/krml.do: pulse/raw/everparse.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all %.do

.PHONY: interface snapshot test-snapshot

clean: pulse/det.clean pulse/nondet.clean

.PHONY: clean

clean-verify: spec.clean spec/raw.clean spec/raw/everparse.clean pulse.clean pulse/raw.clean pulse/raw/everparse.clean pulse/krml.clean

.PHONY: clean-verify

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
