# Custard extraction for CBOR.
#
# Custard is F*'s work-in-progress extraction backend
# (https://github.com/FStarLang/FStar/pull/4395).  Both legs are wired up here:
#
#   * C    -- Custard's direct-to-C backend, replacing F* --codegen krml + karamel.
#   * Rust -- Custard --custard_backend KrmlRust, then karamel as before.
#
# Both are driven from the *same* verified .checked files as the karamel-native
# build, so `verify` is shared and there is no second verification.
#
# Requires an F* built from the `gebner_custard` branch; see
# ../README.custard.md.

CUSTARD_EVERPARSE_SRC ?= $(realpath $(EVERPARSE_SRC_PATH))
_CUSTARD_S := $(CUSTARD_EVERPARSE_SRC)

# The byte_slice backend implementation of CBOR.Pulse.Raw.Slice is selected by
# include path, exactly as in the karamel-native build: slice-c for the C leg,
# slice-rust for the Rust leg.  CBOR_SLICE_BACKEND is already set by the
# c.Makefile / rust.Makefile that includes us, so reuse it.
CUSTARD_SLICE ?= $(CBOR_SLICE_BACKEND)

CUSTARD_INCLUDE_DIRS := \
  $(_CUSTARD_S)/lowparse $(_CUSTARD_S)/lowparse/pulse \
  $(_CUSTARD_S)/cbor/spec $(_CUSTARD_S)/cbor/spec/raw \
  $(_CUSTARD_S)/cbor/spec/raw/everparse \
  $(_CUSTARD_S)/cbor/pulse $(_CUSTARD_S)/cbor/pulse/raw \
  $(_CUSTARD_S)/cbor/pulse/raw/everparse \
  $(_CUSTARD_S)/cbor/pulse/raw/slice-$(CUSTARD_SLICE)

# --already_cached '*,' : Custard consumes the .checked files produced by the
# shared `verify` step and re-checks nothing.
CUSTARD_FSTAR_OPTIONS := \
  --z3version 4.13.3 \
  $(addprefix --include ,$(CUSTARD_INCLUDE_DIRS)) \
  --already_cached '*,' \
  --warn_error -241-342-321-274-272 \
  --ext context_pruning \
  --codegen Custard

CUSTARD_FSTAR := $(FSTAR_EXE) $(CUSTARD_FSTAR_OPTIONS)

# Custard extracts a whole program from its entry points, so every module that
# the karamel-native build names in a `-bundle` `+` list has to be an entry
# module of its own -- a module nothing reachable mentions is simply not
# extracted.  These lists mirror the bundles in c.Makefile and rust.Makefile.
CUSTARD_DET_C_ENTRY := \
  CBOR.Pulse.API.Det.C CBOR.Pulse.API.Det.C.Copy \
  CBOR.Pulse.API.Det.Dummy CBOR.Spec.Constants CBOR.Pulse.API.Det.Type

CUSTARD_DET_C_NO_PREFIX := \
  CBOR.Pulse.API.Det.C CBOR.Pulse.API.Det.Type CBOR.Spec.Constants \
  CBOR.Pulse.Raw.Type CBOR.Pulse.API.Det.C.Copy CBOR.Pulse.Raw.Copy \
  CBOR.Pulse.API.Det.Dummy

CUSTARD_NONDET_C_ENTRY := \
  CBOR.Pulse.API.Nondet.C CBOR.Spec.Constants CBOR.Pulse.API.Nondet.Type

CUSTARD_NONDET_C_NO_PREFIX := \
  CBOR.Pulse.API.Nondet.C CBOR.Pulse.API.Nondet.Type \
  CBOR.Spec.Constants CBOR.Pulse.Raw.Type

CUSTARD_DET_RUST_ENTRY := \
  CBOR.Pulse.API.Det.Rust CBOR.Spec.Constants CBOR.Pulse.Raw.Type \
  CBOR.Pulse.Raw.Slice CBOR.Pulse.API.Det.Type CBOR.Pulse.API.Det.Dummy

CUSTARD_NONDET_RUST_ENTRY := \
  CBOR.Pulse.API.Nondet.Rust CBOR.Spec.Constants CBOR.Pulse.Raw.Type \
  CBOR.Pulse.Raw.Slice CBOR.Pulse.API.Nondet.Type

# Roots for the whole-program walk.  Any module in the corresponding entry list
# would do; these are the API modules the rest is reachable from.
CUSTARD_DET_ROOT    := $(_CUSTARD_S)/cbor/pulse/raw/CBOR.Pulse.API.Det.C.fst
CUSTARD_NONDET_ROOT := $(_CUSTARD_S)/cbor/pulse/raw/CBOR.Pulse.API.Nondet.C.fst
CUSTARD_DET_RUST_ROOT    := $(_CUSTARD_S)/cbor/pulse/raw/CBOR.Pulse.API.Det.Rust.fst
CUSTARD_NONDET_RUST_ROOT := $(_CUSTARD_S)/cbor/pulse/raw/CBOR.Pulse.API.Nondet.Rust.fst
