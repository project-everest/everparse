all: snapshot

EVERPARSE_SRC_PATH ?= $(realpath ..)

# CUSTARD defaults to 1 when the F* in use has Custard and to 0 otherwise.
# Exported so the pulse/{det,nondet} snapshot rules and the pulse/krml
# extraction rules all see the same decision.
include $(EVERPARSE_SRC_PATH)/custard-detect.Makefile
export CUSTARD

interface: spec.do pulse.do

ifeq (1,$(CUSTARD))
snapshot: det/snapshot nondet/snapshot
else
# pulse/{det,nondet}/{c,rust} hold Custard output; karamel's is a different
# shape (CBORxxxType.h, internal/, krmllib.h) and would not be an update of it.
snapshot:
	@echo 'ERROR: the CBOR snapshots are Custard output, and this F* has no Custard.' >&2
	@echo '       Rebuild F* from the gebner_custard branch (FStarLang/FStar#4395);' >&2
	@echo '       see ../cose/README.custard.md.' >&2
	@false
endif

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

# Under CUSTARD=1 the C leg needs no .krml pass at all (Custard goes straight
# to C) and the Rust leg drives karamel itself, so extract-custard does not
# depend on extract-krml.  Chosen in the recipe rather than with ifeq so the
# decision does not depend on where this file is included from.
extract:
	+$(MAKE) $(if $(filter 1,$(CUSTARD)),extract-custard,extract-karamel)

extract-karamel: extract-krml
	+$(MAKE) -C pulse/krml

extract-custard:
	+$(MAKE) -C pulse/krml extract-custard

.PHONY: extract extract-karamel extract-custard

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
