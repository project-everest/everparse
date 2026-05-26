module CBOR.Pulse.Raw.EverParse.Nondet.Compare
#lang-pulse
include CBOR.Spec.Raw.Nondet
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module IT = LowParse.PulseParse.Iterator.Type
module U64 = FStar.UInt64
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen

// === Pure field correspondence between cbor_raw struct fields and raw_data_item ===

// Stronger version of cbor_raw_match_cases_prop that includes value-level facts
let cbor_raw_match_fields_prop (x: cbor_raw) (y: raw_data_item) : prop =
  match x, y with
  | CBOR_Case_Int v, Int64 m rv ->
    v.cbor_int_type == m /\ v.cbor_int_value == rv.value /\ v.cbor_int_size == rv.size
  | CBOR_Case_Simple sv, Simple sv' -> sv == sv'
  | CBOR_Case_String v, String m len _ ->
    v.cbor_string_type == m /\ v.cbor_string_size == len.size /\ SZ.v (S.len v.cbor_string_ptr) == U64.v len.value
  | CBOR_Case_Array v, Array len _ ->
    v.cbor_array_length_size == len.size /\ SZ.v (IT.mixed_list_length v.cbor_array_ptr) == U64.v len.value
  | CBOR_Case_Map v, Map len _ ->
    v.cbor_map_length_size == len.size /\ SZ.v (IT.mixed_list_length v.cbor_map_ptr) == U64.v len.value
  | CBOR_Case_Tagged v, Tagged tag _ -> v.cbor_tagged_tag == tag
  | CBOR_Case_Tagged_Serialized v, Tagged tag _ -> v.cbor_tagged_serialized_tag == tag
  | _, _ -> False

// Helper ghost function: from cbor_raw_match_aux, derive the field correspondence.
// Used by Det.Compare to extract per-constructor field equalities without needing
// to unfold cbor_raw_match itself.
val cbor_raw_match_aux_fields
  (r: perm -> cbor_raw -> raw_data_item -> slprop)
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
: stt_ghost unit emp_inames
    (cbor_raw_match_aux parse_raw_data_item r pm x y)
    (fun _ -> cbor_raw_match_aux parse_raw_data_item r pm x y ** pure (cbor_raw_match_fields_prop x y))

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
