module CBOR.Pulse.Raw.EverParse.Det.Compare.Base
#lang-pulse
include CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open CBOR.Pulse.Raw.Compare.Base
open CBOR.Pulse.Raw.Compare.Bytes
open LowParse.Spec.VCList
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Iterator
open LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module U64 = FStar.UInt64
module I16 = FStar.Int16
module U8 = FStar.UInt8
module Spec = CBOR.Spec.Raw.Base
module NC = CBOR.Pulse.Raw.EverParse.Nondet.Compare
module LPS = LowParse.Pulse.Base
module SCE = CBOR.Pulse.Raw.EverParse.SerializeCborEq

// === Scalar comparison helpers ===

let uint64_compare (x1 x2: U64.t) : Tot I16.t =
  if U64.lt x1 x2
  then (-1s)
  else if U64.gt x1 x2
  then 1s
  else 0s

val impl_raw_uint64_compare
  (_: unit)
: impl_compare_scalar_t u#0 #_ raw_uint64_compare

// === Pure field reading helpers ===

inline_for_extraction
let cbor_raw_int_raw_uint64 (x: cbor_raw) : raw_uint64 =
  match x with
  | CBOR_Case_Int v -> { size = v.cbor_int_size; value = v.cbor_int_value }
  | _ -> { size = 0uy; value = 0UL }

let cbor_raw_int_raw_uint64_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (NC.cbor_raw_match_fields_prop x v))
  (_: squash (Int64? v))
: Lemma (cbor_raw_int_raw_uint64 x == Int64?.v v)
= ()

inline_for_extraction
let cbor_raw_string_len (x: cbor_raw) : raw_uint64 =
  match x with
  | CBOR_Case_String v -> { size = v.cbor_string_size; value = SZ.sizet_to_uint64 (S.len (to_slice v.cbor_string_ptr)) }
  | _ -> { size = 0uy; value = 0UL }

let cbor_raw_string_len_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (NC.cbor_raw_match_fields_prop x v))
  (_: squash (String? v))
: Lemma (cbor_raw_string_len x == String?.len v)
= match x with
  | CBOR_Case_String vx ->
    FStar.Math.Lemmas.small_mod (SZ.v (S.len (to_slice vx.cbor_string_ptr))) (pow2 64)
  | _ -> ()

inline_for_extraction
let cbor_raw_tag_raw_uint64 (x: cbor_raw) : raw_uint64 =
  match x with
  | CBOR_Case_Tagged v -> v.cbor_tagged_tag
  | CBOR_Case_Tagged_Serialized v -> v.cbor_tagged_serialized_tag
  | _ -> { size = 0uy; value = 0UL }

let cbor_raw_tag_raw_uint64_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (NC.cbor_raw_match_fields_prop x v))
  (_: squash (Tagged? v))
: Lemma (cbor_raw_tag_raw_uint64 x == Tagged?.tag v)
= ()

inline_for_extraction
let cbor_raw_array_raw_uint64 (x: cbor_raw) : raw_uint64 =
  match x with
  | CBOR_Case_Array v -> { size = v.cbor_array_length_size; value = SZ.sizet_to_uint64 (IT.mixed_list_length v.cbor_array_ptr) }
  | _ -> { size = 0uy; value = 0UL }

let cbor_raw_array_raw_uint64_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (NC.cbor_raw_match_fields_prop x v))
  (_: squash (Array? v))
: Lemma (cbor_raw_array_raw_uint64 x == Array?.len v)
= match x with
  | CBOR_Case_Array vx ->
    FStar.Math.Lemmas.small_mod (SZ.v (IT.mixed_list_length vx.cbor_array_ptr)) (pow2 64)
  | _ -> ()

inline_for_extraction
let cbor_raw_map_raw_uint64 (x: cbor_raw) : raw_uint64 =
  match x with
  | CBOR_Case_Map v -> { size = v.cbor_map_length_size; value = SZ.sizet_to_uint64 (IT.mixed_list_length v.cbor_map_ptr) }
  | _ -> { size = 0uy; value = 0UL }

let cbor_raw_map_raw_uint64_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (NC.cbor_raw_match_fields_prop x v))
  (_: squash (Map? v))
: Lemma (cbor_raw_map_raw_uint64 x == Map?.len v)
= match x with
  | CBOR_Case_Map vx ->
    FStar.Math.Lemmas.small_mod (SZ.v (IT.mixed_list_length vx.cbor_map_ptr)) (pow2 64)
  | _ -> ()

// === Array/Map spec helpers ===

let cbor_compare_array_total
  (l1 l2: list raw_data_item)
: Tot int
= if List.Tot.length l1 = List.Tot.length l2
  then cbor_compare_array l1 l2
  else 0

let cbor_compare_map_total
  (l1 l2: list (raw_data_item & raw_data_item))
: Tot int
= if List.Tot.length l1 = List.Tot.length l2
  then cbor_compare_map l1 l2
  else 0

let cbor_compare_tagged_total
  (v1 v2: raw_data_item)
: Tot int
= match v1, v2 with
  | Tagged _ p1, Tagged _ p2 -> cbor_compare p1 p2
  | _ -> 0

let array_v (v: raw_data_item) : Tot (list raw_data_item) =
  match v with
  | Array _ l -> l
  | _ -> []

let map_v (v: raw_data_item) : Tot (list (raw_data_item & raw_data_item)) =
  match v with
  | Map _ l -> l
  | _ -> []

// === Fuel-aware compare type ===

inline_for_extraction
noextract [@@noextract_to "krml"]
let compare_cbor_raw_fuel_t (n: Ghost.erased nat) =
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2)
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare v1 v2)))

// === Byte-compare helpers ===

inline_for_extraction
val byte_compare_pts_to_parsed_data_item
  (s1 s2: S.slice byte)
  (#p1: perm) (#v1: Ghost.erased raw_data_item)
  (#p2: perm) (#v2: Ghost.erased raw_data_item)
: stt I16.t
  (PPB.pts_to_parsed parse_raw_data_item s1 #p1 v1 **
   PPB.pts_to_parsed parse_raw_data_item s2 #p2 v2)
  (fun res ->
   PPB.pts_to_parsed parse_raw_data_item s1 #p1 v1 **
   PPB.pts_to_parsed parse_raw_data_item s2 #p2 v2 **
   pure (same_sign (I16.v res) (cbor_compare v1 v2)))

inline_for_extraction
val byte_compare_pts_to_parsed_strong_prefix_data_item
  (f64: squash SZ.fits_u64)
  (s1 s2: S.slice byte)
  (#p1: perm) (#v1: Ghost.erased raw_data_item)
  (#p2: perm) (#v2: Ghost.erased raw_data_item)
: stt I16.t
  (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #p1 v1 **
   PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #p2 v2)
  (fun res ->
   PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #p1 v1 **
   PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #p2 v2 **
   pure (same_sign (I16.v res) (cbor_compare v1 v2)))

unfold
let cbor_compare_pair (kv1 kv2: raw_data_item & raw_data_item) : Tot int =
  let c = cbor_compare (fst kv1) (fst kv2) in
  if c = 0 then cbor_compare (snd kv1) (snd kv2) else c

inline_for_extraction
val byte_compare_pts_to_parsed_pair_data_item
  (f64: squash SZ.fits_u64)
  (s1 s2: S.slice byte)
  (#p1: perm) (#kv1: Ghost.erased (raw_data_item & raw_data_item))
  (#p2: perm) (#kv2: Ghost.erased (raw_data_item & raw_data_item))
: stt I16.t
  (PPB.pts_to_parsed_strong_prefix
     (nondep_then parse_raw_data_item parse_raw_data_item)
     s1 #p1 kv1 **
   PPB.pts_to_parsed_strong_prefix
     (nondep_then parse_raw_data_item parse_raw_data_item)
     s2 #p2 kv2)
  (fun res ->
   PPB.pts_to_parsed_strong_prefix
     (nondep_then parse_raw_data_item parse_raw_data_item)
     s1 #p1 kv1 **
   PPB.pts_to_parsed_strong_prefix
     (nondep_then parse_raw_data_item parse_raw_data_item)
     s2 #p2 kv2 **
   pure (same_sign (I16.v res) (cbor_compare_pair kv1 kv2)))

// === Local type abbreviations for the three callbacks (used by Dispatch) ===

inline_for_extraction noextract [@@noextract_to "krml"]
let compare_cbor_raw_fuel_tagged_local_t (n: Ghost.erased nat) =
  (n_pos: squash (Ghost.reveal n >= 1)) ->
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (Tagged? (Ghost.reveal v1) /\ Tagged? (Ghost.reveal v2)))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare_tagged_total (Ghost.reveal v1) (Ghost.reveal v2))))

inline_for_extraction noextract [@@noextract_to "krml"]
let compare_cbor_raw_fuel_array_local_t (n: Ghost.erased nat) =
  (n_pos: squash (Ghost.reveal n >= 1)) ->
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (len: SZ.t) ->
  (sq: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  )) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (
       Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
       List.Tot.length (array_v (Ghost.reveal v1)) == SZ.v len /\
       List.Tot.length (array_v (Ghost.reveal v2)) == SZ.v len
     ))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare_array_total (array_v (Ghost.reveal v1)) (array_v (Ghost.reveal v2)))))

inline_for_extraction noextract [@@noextract_to "krml"]
let compare_cbor_raw_fuel_map_local_t (n: Ghost.erased nat) =
  (n_pos: squash (Ghost.reveal n >= 1)) ->
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (len: SZ.t) ->
  (sq: squash (
    CBOR_Case_Map? x1 /\ CBOR_Case_Map? x2 /\
    IT.mixed_list_length (CBOR_Case_Map?.v x1).cbor_map_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Map?.v x2).cbor_map_ptr == len
  )) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (
       Map? (Ghost.reveal v1) /\ Map? (Ghost.reveal v2) /\
       List.Tot.length (map_v (Ghost.reveal v1)) == SZ.v len /\
       List.Tot.length (map_v (Ghost.reveal v2)) == SZ.v len
     ))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare_map_total (map_v (Ghost.reveal v1)) (map_v (Ghost.reveal v2)))))
