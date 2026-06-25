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

# Build the two CBOR.Pulse.Raw.Slice backend implementations (each verified by its
# own Makefile under pulse/raw/slice-{c,rust}) before invoking krml: the krml passes
# treat the slice as already cached (ALREADY_CACHED='*,-CBOR,CBOR.Pulse.Raw.Slice,',
# matching pulse/krml/Makefile), so krml's dependency scan requires the slice .checked
# to already exist. On separate recipe lines, hence sequential, so the two backend
# builds never race on the shared CBOR.Pulse.Raw.Slice.fsti.checked.
slice-c:
	+$(MAKE) -C pulse/raw/slice-c

slice-rust:
	+$(MAKE) -C pulse/raw/slice-rust

.PHONY: slice-c slice-rust

extract-krml: slice-c slice-rust
	+$(MAKE) -C pulse/krml extract-krml

.PHONY: extract-krml

extract: extract-krml
	+$(MAKE) -C pulse/krml

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

clean-verify: pulse/raw/slice-c.clean pulse/raw/slice-rust.clean

.PHONY: clean-verify

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
