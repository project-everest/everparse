all: snapshot

interface: spec.do pulse.do

snapshot: extract
	+$(MAKE) -C pulse/det $@

test-snapshot: extract
	+$(MAKE) -C pulse/det $@

extract:
	+$(MAKE) -C pulse/det/krml ALREADY_CACHED='*,-CBOR,'

.PHONY: extract

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

clean: pulse/det.clean

.PHONY: clean

clean-verify: spec.clean spec/raw.clean spec/raw/everparse.clean pulse.clean pulse/raw.clean pulse/raw/everparse.clean pulse/det/krml.clean

.PHONY: clean-verify

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
