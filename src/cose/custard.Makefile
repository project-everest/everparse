# Custard extraction for COSE.
#
# Custard is F*'s work-in-progress extraction backend
# (https://github.com/FStarLang/FStar/pull/4395).  Two legs are wired up here:
#
#   * C    -- Custard's direct-to-C backend, replacing F* --codegen krml + karamel.
#   * Rust -- Custard --custard_backend KrmlRust, then karamel as before.
#
# Both are driven from the *same* verified .checked files as the karamel-native
# build, so `verify` is shared and there is no second verification.
#
# Requires an F* built from the `gebner_custard` branch; see README.custard.md.

CUSTARD_EVERPARSE_SRC ?= $(realpath ../..)
_CUSTARD_S := $(CUSTARD_EVERPARSE_SRC)

# slice-c for the C leg, slice-rust for the Rust leg.
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

# --already_cached '*,' : Custard consumes the .checked files produced by the
# shared `verify` step and re-checks nothing.
#
# The warn_error list matches the karamel-native build's, plus 321/274/272,
# which Custard raises for cross-module inlining decisions that are not errors
# here.
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
# module nothing reachable mentions is simply not extracted.  A `-bundle
# 'M=[...]'` naming an absent module is fatal to karamel, so an omission here
# surfaces as a bundle error rather than as missing code.
CUSTARD_C_ENTRY_MODULES := \
  COSE.Format COSE.EverCrypt \
  CBOR.Pulse.API.Det.C CBOR.Spec.Constants \
  CBOR.Pulse.API.Det.Type CBOR.Pulse.API.Det.Dummy

# Mirrors the karamel-native build's -no-prefix flags, so the emitted C names
# match the snapshot in ../c.  karamel's -no-prefix Abort has no counterpart
# here: --custard_c_no_prefix covers definitions, not assume vals, so listing
# Abort changes nothing.  Abort.abort is instead realized by the consumers,
# which define Abort_abort; see README.custard.md.
CUSTARD_C_NO_PREFIX := \
  CBOR.Pulse.API.Det.C CBOR.Pulse.API.Det.Type \
  CBOR.Spec.Constants CBOR.Pulse.API.Det.Dummy

CUSTARD_RUST_ENTRY_MODULES := \
  COSE.Format CommonPulse EverCrypt.Ed25519 \
  CBOR.Pulse.API.Det.Rust CBOR.Spec.Constants \
  CBOR.Pulse.Raw.Type CBOR.Pulse.Raw.Slice CBOR.Pulse.API.Det.Type
