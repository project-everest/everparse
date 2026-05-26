module CBOR.Pulse.Raw.EverParse.Nondet.Compare
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen

// === Top-level structural-equality comparator over cbor_raw ===
// Uses basic_data_model (always false), so reduces to plain structural equivalence.
// map_bound = None means unbounded; map_bound = Some n caps map-comparison depth.

inline_for_extraction
val compare_cbor_raw_basic
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
: stt (option bool)
    (cbor_raw_match pm1 x1 v1 **
     cbor_raw_match pm2 x2 v2)
    (fun res ->
      cbor_raw_match pm1 x1 v1 **
      cbor_raw_match pm2 x2 v2 **
      pure (res == check_equiv basic_data_model (NG.option_sz_v map_bound) v1 v2))
