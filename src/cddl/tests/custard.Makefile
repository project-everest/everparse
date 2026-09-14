# Custard extraction for the CDDL test corpora.
#
# Custard is F*'s work-in-progress extraction backend
# (https://github.com/FStarLang/FStar/pull/4395).  See ../../README.custard.md.
#
# Unlike cbor and cose, nothing here is snapshotted: these are tests, and the
# generated C is rebuilt from the .cddl sources on every run.  So the only
# thing this fragment has to do is produce a translation unit the existing
# consumers (client.c and friends) can be linked against.
#
# Custard emits one translation unit per entry-point set, with no separate
# CBOR library to link: the CBOR det API is folded in, exactly as it is for
# cose.  The karamel-native build instead bundles CBOR into CBORDetAPI.h and
# links ../../../cbor/pulse/det/c/CBORDet.o, so the Custard leg has neither
# that header nor that object.  A one-line shim supplies the name for
# consumers that spell it (see custard-cbor-shim below).

CUSTARD_EVERPARSE_SRC ?= $(realpath ../../..)
_CUSTARD_S := $(CUSTARD_EVERPARSE_SRC)

# The CDDL tests all drive the deterministic CBOR API, whose abstract slice
# seam is realized by slice-c.
CUSTARD_SLICE ?= c

CUSTARD_INCLUDE_DIRS := \
  $(_CUSTARD_S)/lowparse $(_CUSTARD_S)/lowparse/pulse \
  $(_CUSTARD_S)/cbor/spec $(_CUSTARD_S)/cbor/spec/raw \
  $(_CUSTARD_S)/cbor/spec/raw/everparse \
  $(_CUSTARD_S)/cbor/pulse $(_CUSTARD_S)/cbor/pulse/raw \
  $(_CUSTARD_S)/cbor/pulse/raw/everparse \
  $(_CUSTARD_S)/cbor/pulse/raw/slice-$(CUSTARD_SLICE) \
  $(_CUSTARD_S)/cddl/spec $(_CUSTARD_S)/cddl/pulse $(_CUSTARD_S)/cddl/tool \
  $(CURDIR) $(CURDIR)/$(OUTPUT_DIRECTORY)

# --already_cached '*,' : Custard consumes the .checked files the shared
# `verify` step produced and re-checks nothing.
CUSTARD_FSTAR_OPTIONS := \
  --z3version 4.13.3 \
  $(addprefix --include ,$(CUSTARD_INCLUDE_DIRS)) \
  --already_cached '*,' \
  --warn_error -241-342-321-274-272 \
  --ext context_pruning \
  --codegen Custard

CUSTARD_FSTAR := $(FSTAR_EXE) $(CUSTARD_FSTAR_OPTIONS)

# Every module named in a karamel `-bundle` `+` list has to be an entry module
# of its own: Custard extracts a whole program from its entry points, and a
# module nothing reachable mentions is simply not extracted.
CUSTARD_CBOR_DET_ENTRY_MODULES := \
  CBOR.Pulse.API.Det.C CBOR.Spec.Constants \
  CBOR.Pulse.API.Det.Type CBOR.Pulse.API.Det.Dummy

# The Rust leg is Custard --custard_backend KrmlRust followed by karamel
# unchanged, so what karamel needs is the same set of modules it used to get
# from F* --codegen krml: the union of the `+` lists of its -bundle flags.
# Note CBOR.Pulse.Raw.Slice, which the C leg does not need: the Rust leg's
# slice seam is realized by slice-rust (CUSTARD_SLICE := rust), and that
# module has to be reachable for karamel to print the slice operations.
CUSTARD_CBOR_RUST_ENTRY_MODULES := \
  CBOR.Pulse.API.Det.Rust CBOR.Spec.Constants \
  CBOR.Pulse.Raw.Type CBOR.Pulse.Raw.Slice CBOR.Pulse.API.Det.Type

# Mirrors the karamel-native build's -no-prefix flags, so the emitted C names
# are the ones the consumers already spell.  CBOR.Pulse.Raw.Type is here for a
# reason karamel did not need: the karamel build takes cbor_det_t and cbor_raw
# from the cbor snapshot's CBORDetType.h, which is on its include path, and
# emits neither itself.  Custard folds the det API into this unit, so the unit
# has to publish those names, and it publishes them unprefixed only if the
# module they come from is listed.  The list is cbor's own det C one (see
# ../../cbor/custard.Makefile) so the surface is identical either way.
#
# Abort is in the list for the same reason it is in karamel's: Abort.abort is
# an assume val realized by libc's abort(), so it must be emitted unprefixed
# to link.
CUSTARD_C_NO_PREFIX = \
  $(CUSTARD_CBOR_DET_ENTRY_MODULES) CBOR.Pulse.Raw.Type Abort

# Deferred, not immediate: the including Makefile sets
# CUSTARD_C_ENTRY_MODULES after this fragment, so that it can name
# $(CUSTARD_CBOR_DET_ENTRY_MODULES) alongside its own modules.
CUSTARD_C_FLAGS = \
  --custard_backend C --custard_monomorphize_types true \
  $(addprefix --custard_entry_module ,$(CUSTARD_C_ENTRY_MODULES)) \
  $(addprefix --custard_c_no_prefix ,$(CUSTARD_C_NO_PREFIX))

# The karamel-native build publishes the det CBOR API as CBORDetAPI.h and its
# types as CBORDetType.h.  Custard folds both into the single translation unit
# it emits, so a consumer that includes either by name needs something to
# find.  One line each, pointing at the unit that now carries the
# declarations, keeps those consumers unmodified.
#
# $(1) is the directory to write them into, $(2) the emitted header's name.
define custard-cbor-shim
	printf '/* Generated: Custard folds the det CBOR API into %s. */\n#include "%s"\n' \
	  '$(2)' '$(2)' > $(1)/CBORDetAPI.h
	printf '/* Generated: Custard folds the det CBOR types into %s. */\n#include "%s"\n' \
	  '$(2)' '$(2)' > $(1)/CBORDetType.h
endef

# The variant for a directory that holds *several* Custard units side by side
# (src/cddl/tests/unit: one per .cddl file).  There the redirect above cannot
# work -- there is one CBORDetAPI.h but many unit headers, and each unit
# publishes the whole det API, so redirecting to any one of them would drag a
# second copy of those declarations into every other unit's consumer.
#
# It does not need to redirect anywhere.  Every consumer in that directory
# includes its own unit's header, which already carries the folded-in det API,
# before it includes CBORDetAPI.h.  So the shim only has to exist.
#
# $(1) is the directory to write them into.
define custard-cbor-shim-empty
	printf '/* Generated: intentionally empty.  Custard folds the det CBOR API\n   into each unit header, which this consumer already includes. */\n' \
	  > $(1)/CBORDetAPI.h
	printf '/* Generated: intentionally empty.  Custard folds the det CBOR types\n   into each unit header, which this consumer already includes. */\n' \
	  > $(1)/CBORDetType.h
endef
