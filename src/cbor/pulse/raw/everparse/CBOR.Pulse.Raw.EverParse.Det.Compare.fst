module CBOR.Pulse.Raw.EverParse.Det.Compare
#lang-pulse
include CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
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

// === Type for compare function ===

inline_for_extraction
noextract [@@noextract_to "krml"]
let compare_cbor_raw_t =
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
    (cbor_raw_match pm1 x1 v1 **
     cbor_raw_match pm2 x2 v2)
    (fun res ->
      cbor_raw_match pm1 x1 v1 **
      cbor_raw_match pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare v1 v2)))

// === Scalar comparison helpers ===

let uint64_compare (x1 x2: U64.t) : Tot I16.t =
  if U64.lt x1 x2
  then (-1s)
  else if U64.gt x1 x2
  then 1s
  else 0s

#push-options "--z3rlimit 32"

fn impl_raw_uint64_compare
  (_: unit)
: impl_compare_scalar_t u#0 #_ raw_uint64_compare
= (x1: _)
  (x2: _)
{
  let c = impl_uint8_compare () x1.size x2.size;
  if (c = 0s) {
    uint64_compare x1.value x2.value
  } else {
    c
  }
}

#pop-options

// === Pure field reading helpers ===
// These read concrete struct fields — cbor_raw_match_fields_prop connects them to spec

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

let cbor_raw_string_len (x: cbor_raw) : raw_uint64 =
  match x with
  | CBOR_Case_String v -> { size = v.cbor_string_size; value = SZ.sizet_to_uint64 (S.len v.cbor_string_ptr) }
  | _ -> { size = 0uy; value = 0UL }

let cbor_raw_string_len_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (NC.cbor_raw_match_fields_prop x v))
  (_: squash (String? v))
: Lemma (cbor_raw_string_len x == String?.len v)
= match x with
  | CBOR_Case_String vx ->
    FStar.Math.Lemmas.small_mod (SZ.v (S.len vx.cbor_string_ptr)) (pow2 64)
  | _ -> ()

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

// === Array pairwise comparison ===

// Total wrapper for cbor_compare_array (returns 0 when lengths don't match)
let cbor_compare_array_total
  (l1 l2: list raw_data_item)
: Tot int
= if List.Tot.length l1 = List.Tot.length l2
  then cbor_compare_array l1 l2
  else 0

// Same for map
let cbor_compare_map_total
  (l1 l2: list (raw_data_item & raw_data_item))
: Tot int
= if List.Tot.length l1 = List.Tot.length l2
  then cbor_compare_map l1 l2
  else 0

// Total accessors for array/map content
let array_v (v: raw_data_item) : Tot (list raw_data_item) =
  match v with
  | Array _ l -> l
  | _ -> []

let map_v (v: raw_data_item) : Tot (list (raw_data_item & raw_data_item)) =
  match v with
  | Map _ l -> l
  | _ -> []

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
fn compare_cbor_raw_array_case
  (f64: squash SZ.fits_u64)
  (ih: compare_cbor_raw_t)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (len: SZ.t)
  (_: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  ))
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (
    Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
    List.Tot.length (array_v (Ghost.reveal v1)) == SZ.v len /\
    List.Tot.length (array_v (Ghost.reveal v2)) == SZ.v len
  )
returns res: I16.t
ensures
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (same_sign (I16.v res) (cbor_compare_array_total (array_v (Ghost.reveal v1)) (array_v (Ghost.reveal v2))))
{
  let zcp = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read 1.0R f64) ();
  // Get arrays
  let ar_ml1 = cbor_raw_get_array pm1 x1 ();
  with pm1_a ar1 . assert (
    I.mixed_list_match cbor_raw_match parse_raw_data_item pm1_a ar_ml1 ar1 **
    trade (I.mixed_list_match cbor_raw_match parse_raw_data_item pm1_a ar_ml1 ar1)
          (cbor_raw_match pm1 x1 v1)
  );
  let ar_ml2 = cbor_raw_get_array pm2 x2 ();
  with pm2_a ar2 . assert (
    I.mixed_list_match cbor_raw_match parse_raw_data_item pm2_a ar_ml2 ar2 **
    trade (I.mixed_list_match cbor_raw_match parse_raw_data_item pm2_a ar_ml2 ar2)
          (cbor_raw_match pm2 x2 v2)
  );
  // Start iterators
  let it1_init = I.iterator_start cbor_raw_match parse_raw_data_item (jump_raw_data_item f64) pm1_a ar_ml1 ar1
    NC.cbor_raw_match_share_t NC.cbor_raw_match_gather_t;
  Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
  let it2_init = I.iterator_start cbor_raw_match parse_raw_data_item (jump_raw_data_item f64) pm2_a ar_ml2 ar2
    NC.cbor_raw_match_share_t NC.cbor_raw_match_gather_t;
  Trade.trans _ _ (cbor_raw_match pm2 x2 v2);
  // Loop state
  let mut r_it1 = it1_init;
  let mut r_it2 = it2_init;
  let mut r_acc : I16.t = 0s;
  let mut r_cnt = 0sz;
  // Pairwise comparison loop
  while (
    let acc = !r_acc;
    let cnt = !r_cnt;
    (SZ.lt cnt len && acc = 0s)
  ) invariant exists* it1c it2c (acc_c: I16.t) cnt_c rem1 rem2 pm1c pm2c .
    R.pts_to r_it1 it1c **
    R.pts_to r_it2 it2c **
    R.pts_to r_acc acc_c **
    R.pts_to r_cnt cnt_c **
    I.iterator_match cbor_raw_match parse_raw_data_item pm1c it1c rem1 **
    I.iterator_match cbor_raw_match parse_raw_data_item pm2c it2c rem2 **
    trade (I.iterator_match cbor_raw_match parse_raw_data_item pm1c it1c rem1)
          (cbor_raw_match pm1 x1 v1) **
    trade (I.iterator_match cbor_raw_match parse_raw_data_item pm2c it2c rem2)
          (cbor_raw_match pm2 x2 v2) **
    pure (
      SZ.v cnt_c <= SZ.v len /\
      List.Tot.length rem1 == SZ.v len - SZ.v cnt_c /\
      List.Tot.length rem2 == SZ.v len - SZ.v cnt_c /\
      Ghost.reveal ar1 == array_v (Ghost.reveal v1) /\
      Ghost.reveal ar2 == array_v (Ghost.reveal v2) /\
      (I16.v acc_c == 0 ==>
        cbor_compare_array_total (Ghost.reveal ar1) (Ghost.reveal ar2) ==
        cbor_compare_array_total rem1 rem2) /\
      (I16.v acc_c <> 0 ==>
        same_sign (I16.v acc_c) (cbor_compare_array_total (Ghost.reveal ar1) (Ghost.reveal ar2)))
    )
  {
    let e1 = I.iterator_next cbor_raw_match parse_raw_data_item (jump_raw_data_item f64) _ r_it1 _ _ NC.cbor_raw_match_share_t NC.cbor_raw_match_gather_t zcp;
    unfold (I.iterator_next_post cbor_raw_match parse_raw_data_item _ r_it1 _ _ e1);
    with pmv1 hdv1 tl1 it1n pm1n . assert (
      cbor_raw_match pmv1 e1 hdv1 **
      R.pts_to r_it1 it1n **
      I.iterator_match cbor_raw_match parse_raw_data_item pm1n it1n tl1
    );
    Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
    let e2 = I.iterator_next cbor_raw_match parse_raw_data_item (jump_raw_data_item f64) _ r_it2 _ _ NC.cbor_raw_match_share_t NC.cbor_raw_match_gather_t zcp;
    unfold (I.iterator_next_post cbor_raw_match parse_raw_data_item _ r_it2 _ _ e2);
    with pmv2 hdv2 tl2 it2n pm2n . assert (
      cbor_raw_match pmv2 e2 hdv2 **
      R.pts_to r_it2 it2n **
      I.iterator_match cbor_raw_match parse_raw_data_item pm2n it2n tl2
    );
    Trade.trans _ _ (cbor_raw_match pm2 x2 v2);
    // Compare the pair
    let pair_res = ih e1 e2;
    // Feed back element matches
    Trade.elim_hyp_l _ _ (cbor_raw_match pm1 x1 v1);
    Trade.elim_hyp_l _ _ (cbor_raw_match pm2 x2 v2);
    // Update acc and cnt
    let old_cnt = !r_cnt;
    r_acc := pair_res;
    r_cnt := SZ.add old_cnt 1sz;
  };
  // After loop: trade back
  Trade.elim _ (cbor_raw_match pm1 x1 v1);
  Trade.elim _ (cbor_raw_match pm2 x2 v2);
  !r_acc
}

#pop-options

// === Map pairwise comparison ===

// Helper: split a cbor_map_entry_vmatch into key and value matches
ghost fn cbor_map_entry_vmatch_elim
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm)
  (#pair: Ghost.erased (raw_data_item & raw_data_item))
requires NC.cbor_map_entry_vmatch pm entry pair
ensures
  cbor_raw_match pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)) **
  cbor_raw_match pm entry.cbor_map_entry_value (snd (Ghost.reveal pair))
{
  unfold (NC.cbor_map_entry_vmatch pm entry pair);
  unfold (cbor_map_entry_match cbor_raw_match pm entry (Ghost.reveal pair));
  unfold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry (Ghost.reveal pair));
  unfold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd (Ghost.reveal pair)));
  rewrite (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst (Ghost.reveal pair)))
    as (cbor_raw_match pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)));
  rewrite (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd (Ghost.reveal pair)))
    as (cbor_raw_match pm entry.cbor_map_entry_value (snd (Ghost.reveal pair)));
}

// Helper: fold back a cbor_map_entry_vmatch from key and value matches
ghost fn cbor_map_entry_vmatch_intro
  (entry: cbor_map_entry cbor_raw)
  (pm: perm)
  (pair: Ghost.erased (raw_data_item & raw_data_item))
requires
  cbor_raw_match pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)) **
  cbor_raw_match pm entry.cbor_map_entry_value (snd (Ghost.reveal pair))
ensures NC.cbor_map_entry_vmatch pm entry pair
{
  rewrite (cbor_raw_match pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)))
    as (cbor_raw_match pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst (Ghost.reveal pair)));
  rewrite (cbor_raw_match pm entry.cbor_map_entry_value (snd (Ghost.reveal pair)))
    as (cbor_raw_match pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd (Ghost.reveal pair)));
  fold (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj entry (snd (Ghost.reveal pair)));
  fold (vmatch_pair_with_proj (cbor_raw_match pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match pm) cbor_map_entry_value_proj) entry (Ghost.reveal pair));
  fold (cbor_map_entry_match cbor_raw_match pm entry (Ghost.reveal pair));
  fold (NC.cbor_map_entry_vmatch pm entry pair);
}

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
fn compare_cbor_raw_map_case
  (f64: squash SZ.fits_u64)
  (ih: compare_cbor_raw_t)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (len: SZ.t)
  (_: squash (
    CBOR_Case_Map? x1 /\ CBOR_Case_Map? x2 /\
    IT.mixed_list_length (CBOR_Case_Map?.v x1).cbor_map_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Map?.v x2).cbor_map_ptr == len
  ))
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (
    Map? (Ghost.reveal v1) /\ Map? (Ghost.reveal v2) /\
    List.Tot.length (map_v (Ghost.reveal v1)) == SZ.v len /\
    List.Tot.length (map_v (Ghost.reveal v2)) == SZ.v len
  )
returns res: I16.t
ensures
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (same_sign (I16.v res) (cbor_compare_map_total (map_v (Ghost.reveal v1)) (map_v (Ghost.reveal v2))))
{
  let zcp_pair = NC.cbor_map_entry_zero_copy_parse f64;
  // Get maps
  let map_ml1 = cbor_raw_get_map pm1 x1 ();
  with pm1_m map1_entries . assert (
    I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match cbor_raw_match pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries **
    trade (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match cbor_raw_match pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
          (cbor_raw_match pm1 x1 v1)
  );
  rewrite
    (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match cbor_raw_match pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
    as (I.mixed_list_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries);
  rewrite
    (trade
      (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match cbor_raw_match pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
      (cbor_raw_match pm1 x1 v1))
    as (trade
      (I.mixed_list_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
      (cbor_raw_match pm1 x1 v1));
  let map_ml2 = cbor_raw_get_map pm2 x2 ();
  with pm2_m map2_entries . assert (
    I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match cbor_raw_match pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries **
    trade (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match cbor_raw_match pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
          (cbor_raw_match pm2 x2 v2)
  );
  rewrite
    (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match cbor_raw_match pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
    as (I.mixed_list_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries);
  rewrite
    (trade
      (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match cbor_raw_match pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
      (cbor_raw_match pm2 x2 v2))
    as (trade
      (I.mixed_list_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
      (cbor_raw_match pm2 x2 v2));
  // Start iterators
  let it1_init = I.iterator_start NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64)) pm1_m map_ml1 map1_entries
    NC.cbor_map_entry_vmatch_share_wrapper NC.cbor_map_entry_vmatch_gather_wrapper;
  Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
  let it2_init = I.iterator_start NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64)) pm2_m map_ml2 map2_entries
    NC.cbor_map_entry_vmatch_share_wrapper NC.cbor_map_entry_vmatch_gather_wrapper;
  Trade.trans _ _ (cbor_raw_match pm2 x2 v2);
  // Loop state
  let mut r_it1 = it1_init;
  let mut r_it2 = it2_init;
  let mut r_acc : I16.t = 0s;
  let mut r_cnt = 0sz;
  // Pairwise comparison loop
  while (
    let acc = !r_acc;
    let cnt = !r_cnt;
    (SZ.lt cnt len && acc = 0s)
  ) invariant exists* it1c it2c (acc_c: I16.t) cnt_c rem1 rem2 pm1c pm2c .
    R.pts_to r_it1 it1c **
    R.pts_to r_it2 it2c **
    R.pts_to r_acc acc_c **
    R.pts_to r_cnt cnt_c **
    I.iterator_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm1c it1c rem1 **
    I.iterator_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm2c it2c rem2 **
    trade (I.iterator_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm1c it1c rem1)
          (cbor_raw_match pm1 x1 v1) **
    trade (I.iterator_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm2c it2c rem2)
          (cbor_raw_match pm2 x2 v2) **
    pure (
      SZ.v cnt_c <= SZ.v len /\
      List.Tot.length rem1 == SZ.v len - SZ.v cnt_c /\
      List.Tot.length rem2 == SZ.v len - SZ.v cnt_c /\
      Ghost.reveal map1_entries == map_v (Ghost.reveal v1) /\
      Ghost.reveal map2_entries == map_v (Ghost.reveal v2) /\
      (I16.v acc_c == 0 ==>
        cbor_compare_map_total (Ghost.reveal map1_entries) (Ghost.reveal map2_entries) ==
        cbor_compare_map_total rem1 rem2) /\
      (I16.v acc_c <> 0 ==>
        same_sign (I16.v acc_c) (cbor_compare_map_total (Ghost.reveal map1_entries) (Ghost.reveal map2_entries)))
    )
  {
    let e1 = I.iterator_next NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64)) _ r_it1 _ _ NC.cbor_map_entry_vmatch_share_wrapper NC.cbor_map_entry_vmatch_gather_wrapper zcp_pair;
    unfold (I.iterator_next_post NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) _ r_it1 _ _ e1);
    with pmv1 hdv1 tl1 it1n pm1n . assert (
      NC.cbor_map_entry_vmatch pmv1 e1 hdv1 **
      R.pts_to r_it1 it1n **
      I.iterator_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm1n it1n tl1
    );
    Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
    let e2 = I.iterator_next NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64)) _ r_it2 _ _ NC.cbor_map_entry_vmatch_share_wrapper NC.cbor_map_entry_vmatch_gather_wrapper zcp_pair;
    unfold (I.iterator_next_post NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) _ r_it2 _ _ e2);
    with pmv2 hdv2 tl2 it2n pm2n . assert (
      NC.cbor_map_entry_vmatch pmv2 e2 hdv2 **
      R.pts_to r_it2 it2n **
      I.iterator_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm2n it2n tl2
    );
    Trade.trans _ _ (cbor_raw_match pm2 x2 v2);
    // Split map entry into key + value
    cbor_map_entry_vmatch_elim e1;
    cbor_map_entry_vmatch_elim e2;
    // Compare keys
    let ck = ih e1.cbor_map_entry_key e2.cbor_map_entry_key;
    if (ck = 0s) {
      // Keys equal, compare values
      let cv = ih e1.cbor_map_entry_value e2.cbor_map_entry_value;
      // Fold back entries
      cbor_map_entry_vmatch_intro e1 pmv1 hdv1;
      cbor_map_entry_vmatch_intro e2 pmv2 hdv2;
      // Feed back entry matches
      Trade.elim_hyp_l _ _ (cbor_raw_match pm1 x1 v1);
      Trade.elim_hyp_l _ _ (cbor_raw_match pm2 x2 v2);
      // Update acc and cnt
      let old_cnt = !r_cnt;
      r_acc := cv;
      r_cnt := SZ.add old_cnt 1sz;
    } else {
      // Keys different — fold back entries
      cbor_map_entry_vmatch_intro e1 pmv1 hdv1;
      cbor_map_entry_vmatch_intro e2 pmv2 hdv2;
      // Feed back entry matches
      Trade.elim_hyp_l _ _ (cbor_raw_match pm1 x1 v1);
      Trade.elim_hyp_l _ _ (cbor_raw_match pm2 x2 v2);
      // Update acc and cnt
      let old_cnt = !r_cnt;
      r_acc := ck;
      r_cnt := SZ.add old_cnt 1sz;
    };
  };
  // After loop: trade back
  Trade.elim _ (cbor_raw_match pm1 x1 v1);
  Trade.elim _ (cbor_raw_match pm2 x2 v2);
  !r_acc
}

#pop-options

// === Body function ===

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
fn cbor_compare_body
  (f64: squash SZ.fits_u64)
  (ih: compare_cbor_raw_t)
: compare_cbor_raw_t
=
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
{
  cbor_raw_match_cases pm1 x1;
  cbor_raw_match_cases pm2 x2;
  NC.cbor_raw_match_fields pm1 x1;
  NC.cbor_raw_match_fields pm2 x2;
  let ty1 = cbor_raw_get_major_type pm1 x1;
  let ty2 = cbor_raw_get_major_type pm2 x2;
  let c = impl_uint8_compare () ty1 ty2;
  if (c = 0s) {
    if (ty1 = cbor_major_type_uint64 || ty1 = cbor_major_type_neg_int64) {
      let ru1 = cbor_raw_int_raw_uint64 x1;
      let ru2 = cbor_raw_int_raw_uint64 x2;
      cbor_raw_int_raw_uint64_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_int_raw_uint64_eq x2 (Ghost.reveal v2) () ();
      impl_raw_uint64_compare () ru1 ru2
    } else if (ty1 = cbor_major_type_byte_string || ty1 = cbor_major_type_text_string) {
      let len1 = cbor_raw_string_len x1;
      let len2 = cbor_raw_string_len x2;
      cbor_raw_string_len_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_string_len_eq x2 (Ghost.reveal v2) () ();
      let c : I16.t = impl_raw_uint64_compare () len1 len2;
      if (c = 0s) {
        let s1 = cbor_raw_get_string pm1 x1 ();
        let s2 = cbor_raw_get_string pm2 x2 ();
        let res = lex_compare_bytes s1 s2;
        Trade.elim _ (cbor_raw_match pm1 x1 v1);
        Trade.elim _ (cbor_raw_match pm2 x2 v2);
        res
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_tagged) {
      let tag1 = cbor_raw_tag_raw_uint64 x1;
      let tag2 = cbor_raw_tag_raw_uint64 x2;
      cbor_raw_tag_raw_uint64_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_tag_raw_uint64_eq x2 (Ghost.reveal v2) () ();
      let c = impl_raw_uint64_compare () tag1 tag2;
      if (c = 0s) {
        let pl1 = cbor_raw_get_tagged_payload pm1 x1 f64 ();
        let pl2 = cbor_raw_get_tagged_payload pm2 x2 f64 ();
        let res = ih pl1 pl2;
        Trade.elim _ (cbor_raw_match pm1 x1 v1);
        Trade.elim _ (cbor_raw_match pm2 x2 v2);
        res
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_array) {
      let len1 = cbor_raw_array_raw_uint64 x1;
      let len2 = cbor_raw_array_raw_uint64 x2;
      cbor_raw_array_raw_uint64_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_array_raw_uint64_eq x2 (Ghost.reveal v2) () ();
      let c = impl_raw_uint64_compare () len1 len2;
      if (c = 0s) {
        let len_sz = SZ.uint64_to_sizet len1.value;
        compare_cbor_raw_array_case f64 ih x1 x2 len_sz ()
      } else {
        c
      }
    } else if (ty1 = cbor_major_type_map) {
      let len1 = cbor_raw_map_raw_uint64 x1;
      let len2 = cbor_raw_map_raw_uint64 x2;
      cbor_raw_map_raw_uint64_eq x1 (Ghost.reveal v1) () ();
      cbor_raw_map_raw_uint64_eq x2 (Ghost.reveal v2) () ();
      let c = impl_raw_uint64_compare () len1 len2;
      if (c = 0s) {
        let len_sz = SZ.uint64_to_sizet len1.value;
        compare_cbor_raw_map_case f64 ih x1 x2 len_sz ()
      } else {
        c
      }
    } else {
      // Simple value
      let sv1 = CBOR_Case_Simple?.v x1;
      let sv2 = CBOR_Case_Simple?.v x2;
      impl_uint8_compare () sv1 sv2
    }
  } else {
    c
  }
}

#pop-options

// === Recursive entry point ===

// === Old non-fuel recursive entry point: still defined so existing helpers above
// remain reachable. The exported impl_cbor_compare further below delegates to the
// fuel-aware version (impl_cbor_compare_fuel). ===

fn rec impl_cbor_compare_norec
  (f64: squash SZ.fits_u64)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2
returns res: I16.t
ensures
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (same_sign (I16.v res) (cbor_compare v1 v2))
{
  cbor_compare_body f64 (impl_cbor_compare_norec f64) x1 x2
}

// === Fuel-aware compare type ===

inline_for_extraction
noextract [@@noextract_to "krml"]
let compare_cbor_raw_fuel_t (n: nat) =
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt I16.t
    (cbor_raw_match_fuel n pm1 x1 v1 **
     cbor_raw_match_fuel n pm2 x2 v2)
    (fun res ->
      cbor_raw_match_fuel n pm1 x1 v1 **
      cbor_raw_match_fuel n pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare v1 v2)))

// === Aux fields helper (parameterized by r) ===
// Analogous to NC.cbor_raw_match_fields, but operates on cbor_raw_match_aux for
// arbitrary r (used with r = cbor_raw_match_fuel (n-1)).

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"

ghost fn cbor_raw_match_aux_fields
  (r: perm -> cbor_raw -> raw_data_item -> slprop)
  (pm: perm) (x: cbor_raw) (#y: Ghost.erased raw_data_item)
requires cbor_raw_match_aux parse_raw_data_item r pm x y
ensures cbor_raw_match_aux parse_raw_data_item r pm x y ** pure (NC.cbor_raw_match_fields_prop x y)
{
  unfold (cbor_raw_match_aux parse_raw_data_item r pm x (Ghost.reveal y));
  unfold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content r parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  unfold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content r parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  unfold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  rewrite
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  let the_prop = cbor_raw_get_header x ==
    Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)));
  let sq = elim_pure_explicit the_prop;
  NC.cbor_raw_match_fields_prop_of_header x (Ghost.reveal y)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))) sq ();
  intro_pure the_prop sq;
  rewrite
    (pure (cbor_raw_get_header x ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))))
    as
    (pure (cbor_raw_get_header (cbor_raw_id_proj.pair_proj_get x) ==
           Some (dfst (synth_raw_data_item_recip (Ghost.reveal y)))));
  fold (cbor_raw_match_header
    (cbor_raw_id_proj.pair_proj_get x)
    (dfst (synth_raw_data_item_recip (Ghost.reveal y))));
  fold (vmatch_dep_pair_with_proj
    cbor_raw_match_header
    cbor_raw_id_proj
    (cbor_raw_match_content r parse_raw_data_item pm)
    x
    (synth_raw_data_item_recip (Ghost.reveal y)));
  fold (vmatch_synth
    (vmatch_dep_pair_with_proj
       cbor_raw_match_header
       cbor_raw_id_proj
       (cbor_raw_match_content r parse_raw_data_item pm))
    synth_raw_data_item_recip
    x (Ghost.reveal y));
  fold (cbor_raw_match_aux parse_raw_data_item r pm x (Ghost.reveal y));
}

#pop-options

// === Byte-compare helpers ===

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

// Compare two cbor data items represented as pts_to_parsed slices (full parse).
// Used for the ESerialized case of an array iterator at fuel n-1.
fn byte_compare_pts_to_parsed_data_item
  (s1 s2: S.slice byte)
  (#p1: perm) (#v1: Ghost.erased raw_data_item)
  (#p2: perm) (#v2: Ghost.erased raw_data_item)
requires
  PPB.pts_to_parsed parse_raw_data_item s1 #p1 v1 **
  PPB.pts_to_parsed parse_raw_data_item s2 #p2 v2
returns res: I16.t
ensures
  PPB.pts_to_parsed parse_raw_data_item s1 #p1 v1 **
  PPB.pts_to_parsed parse_raw_data_item s2 #p2 v2 **
  pure (same_sign (I16.v res) (cbor_compare v1 v2))
{
  cbor_compare_correct (Ghost.reveal v1) (Ghost.reveal v2);
  SCE.serialize_cbor_eq_bare_serialize (Ghost.reveal v1);
  SCE.serialize_cbor_eq_bare_serialize (Ghost.reveal v2);
  PPB.pts_to_parsed_serialized serialize_raw_data_item s1;
  PPB.pts_to_parsed_serialized serialize_raw_data_item s2;
  unfold (LPS.pts_to_serialized serialize_raw_data_item s1 #p1 (Ghost.reveal v1));
  unfold (LPS.pts_to_serialized serialize_raw_data_item s2 #p2 (Ghost.reveal v2));
  let res = lex_compare_bytes s1 s2;
  fold (LPS.pts_to_serialized serialize_raw_data_item s1 #p1 (Ghost.reveal v1));
  fold (LPS.pts_to_serialized serialize_raw_data_item s2 #p2 (Ghost.reveal v2));
  Trade.elim (LPS.pts_to_serialized serialize_raw_data_item s1 #p1 (Ghost.reveal v1))
             (PPB.pts_to_parsed parse_raw_data_item s1 #p1 v1);
  Trade.elim (LPS.pts_to_serialized serialize_raw_data_item s2 #p2 (Ghost.reveal v2))
             (PPB.pts_to_parsed parse_raw_data_item s2 #p2 v2);
  res
}

#pop-options

// Compare two cbor data items each represented as pts_to_parsed_strong_prefix
// slices (only a prefix is the data item; rest is arbitrary). We use the jumper
// to find the exact extent of each data item, byte-compare exact subslices,
// and re-fold strong_prefix at the end.
//
// Used for the ESerialized case of a CBOR_Case_Tagged_Serialized payload, where
// the tagged-serialized struct stores a pts_to_parsed_strong_prefix slice.

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn byte_compare_pts_to_parsed_strong_prefix_data_item
  (f64: squash SZ.fits_u64)
  (s1 s2: S.slice byte)
  (#p1: perm) (#v1: Ghost.erased raw_data_item)
  (#p2: perm) (#v2: Ghost.erased raw_data_item)
requires
  PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #p1 v1 **
  PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #p2 v2
returns res: I16.t
ensures
  PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #p1 v1 **
  PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #p2 v2 **
  pure (same_sign (I16.v res) (cbor_compare v1 v2))
{
  // Step 1: extract exact-extent slices via jumper, with trades back to strong_prefix
  let ex1 = PPB.pts_to_parsed_strong_prefix_to_serialized_trade
              serialize_raw_data_item (jump_raw_data_item f64) s1;
  let ex2 = PPB.pts_to_parsed_strong_prefix_to_serialized_trade
              serialize_raw_data_item (jump_raw_data_item f64) s2;
  // Step 2: byte-compare via the same pattern as the parsed variant
  cbor_compare_correct (Ghost.reveal v1) (Ghost.reveal v2);
  SCE.serialize_cbor_eq_bare_serialize (Ghost.reveal v1);
  SCE.serialize_cbor_eq_bare_serialize (Ghost.reveal v2);
  unfold (LPS.pts_to_serialized serialize_raw_data_item ex1 #p1 (Ghost.reveal v1));
  unfold (LPS.pts_to_serialized serialize_raw_data_item ex2 #p2 (Ghost.reveal v2));
  let res = lex_compare_bytes ex1 ex2;
  fold (LPS.pts_to_serialized serialize_raw_data_item ex1 #p1 (Ghost.reveal v1));
  fold (LPS.pts_to_serialized serialize_raw_data_item ex2 #p2 (Ghost.reveal v2));
  // Step 3: eliminate trades back to strong_prefix
  Trade.elim (LPS.pts_to_serialized serialize_raw_data_item ex1 #p1 (Ghost.reveal v1))
             (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #p1 v1);
  Trade.elim (LPS.pts_to_serialized serialize_raw_data_item ex2 #p2 (Ghost.reveal v2))
             (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #p2 v2);
  res
}

#pop-options

// Pair-level byte-compare for the ESerialized case of a map iterator.
// Each side is a pts_to_parsed_strong_prefix slice of (nondep_then p p),
// where p = parse_raw_data_item. The slice content is bare_serialize s key
// `Seq.append` bare_serialize s value followed by arbitrary suffix.
//
// Postcondition is expressed via the spec-level per-pair compare:
//   if cbor_compare k1 k2 = 0 then cbor_compare v1 v2 else cbor_compare k1 k2

unfold
let cbor_compare_pair (kv1 kv2: raw_data_item & raw_data_item) : Tot int =
  let c = cbor_compare (fst kv1) (fst kv2) in
  if c = 0 then cbor_compare (snd kv1) (snd kv2) else c

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn byte_compare_pts_to_parsed_pair_data_item
  (f64: squash SZ.fits_u64)
  (s1 s2: S.slice byte)
  (#p1: perm) (#kv1: Ghost.erased (raw_data_item & raw_data_item))
  (#p2: perm) (#kv2: Ghost.erased (raw_data_item & raw_data_item))
requires
  PPB.pts_to_parsed_strong_prefix
    (nondep_then parse_raw_data_item parse_raw_data_item)
    s1 #p1 kv1 **
  PPB.pts_to_parsed_strong_prefix
    (nondep_then parse_raw_data_item parse_raw_data_item)
    s2 #p2 kv2
returns res: I16.t
ensures
  PPB.pts_to_parsed_strong_prefix
    (nondep_then parse_raw_data_item parse_raw_data_item)
    s1 #p1 kv1 **
  PPB.pts_to_parsed_strong_prefix
    (nondep_then parse_raw_data_item parse_raw_data_item)
    s2 #p2 kv2 **
  pure (same_sign (I16.v res) (cbor_compare_pair kv1 kv2))
{
  // Step 1: extract exact-extent slices via the pair jumper, with trades back to strong_prefix
  let pair_ser = serialize_nondep_then serialize_raw_data_item serialize_raw_data_item;
  let pair_jmp = jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64);
  let ex1 = PPB.pts_to_parsed_strong_prefix_to_serialized_trade pair_ser pair_jmp s1;
  let ex2 = PPB.pts_to_parsed_strong_prefix_to_serialized_trade pair_ser pair_jmp s2;
  // Step 2: one pure lemma proves the byte-compare ↔ cbor_compare_pair equation.
  SCE.pair_byte_compare_eq_cbor_compare_pair (Ghost.reveal kv1) (Ghost.reveal kv2);
  // Step 3: unfold pts_to_serialized to raw S.pts_to and byte-compare
  unfold (LPS.pts_to_serialized pair_ser ex1 #p1 (Ghost.reveal kv1));
  unfold (LPS.pts_to_serialized pair_ser ex2 #p2 (Ghost.reveal kv2));
  let res = lex_compare_bytes ex1 ex2;
  fold (LPS.pts_to_serialized pair_ser ex1 #p1 (Ghost.reveal kv1));
  fold (LPS.pts_to_serialized pair_ser ex2 #p2 (Ghost.reveal kv2));
  // Step 4: eliminate trades back to strong_prefix
  Trade.elim (LPS.pts_to_serialized pair_ser ex1 #p1 (Ghost.reveal kv1))
             (PPB.pts_to_parsed_strong_prefix
                (nondep_then parse_raw_data_item parse_raw_data_item)
                s1 #p1 kv1);
  Trade.elim (LPS.pts_to_serialized pair_ser ex2 #p2 (Ghost.reveal kv2))
             (PPB.pts_to_parsed_strong_prefix
                (nondep_then parse_raw_data_item parse_raw_data_item)
                s2 #p2 kv2);
  res
}

#pop-options

// === Phase C: map-entry vmatch / share / gather (fuel-aware) ===

// Map entry vmatch at fuel n: cbor_map_entry_match with cbor_raw_match_fuel n
// as the child relation.
let cbor_map_entry_vmatch_fuel
  (n: nat)
  (pm: perm)
  (elem: cbor_map_entry cbor_raw)
  (v: (raw_data_item & raw_data_item))
: Tot slprop
= cbor_map_entry_match (cbor_raw_match_fuel n) pm elem v

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

ghost
fn cbor_map_entry_vmatch_fuel_share_wrapper
  (n: nat)
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm)
  (#pair: (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch_fuel n pm entry pair
ensures cbor_map_entry_vmatch_fuel n (pm /. 2.0R) entry pair **
        cbor_map_entry_vmatch_fuel n (pm /. 2.0R) entry pair
{
  unfold (cbor_map_entry_vmatch_fuel n pm entry pair);
  cbor_map_entry_match_share (cbor_raw_match_fuel n) (cbor_raw_match_fuel_share_t n) entry;
  fold (cbor_map_entry_vmatch_fuel n (pm /. 2.0R) entry pair);
  fold (cbor_map_entry_vmatch_fuel n (pm /. 2.0R) entry pair);
}

ghost
fn cbor_map_entry_vmatch_fuel_gather_wrapper
  (n: nat)
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm) (#pair: (raw_data_item & raw_data_item))
  (#pm': perm) (#pair': (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch_fuel n pm entry pair **
         cbor_map_entry_vmatch_fuel n pm' entry pair'
ensures cbor_map_entry_vmatch_fuel n (pm +. pm') entry pair **
        pure (pair == pair')
{
  // Mirror NC.cbor_map_entry_vmatch_gather_wrapper: unfold everything by hand,
  // call cbor_raw_match_fuel_gather on key/value, then fold back.
  unfold (cbor_map_entry_vmatch_fuel n pm entry pair);
  unfold (cbor_map_entry_vmatch_fuel n pm' entry pair');
  unfold (cbor_map_entry_match (cbor_raw_match_fuel n) pm entry pair);
  unfold (vmatch_pair_with_proj (cbor_raw_match_fuel n pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel n pm) cbor_map_entry_value_proj) entry pair);
  unfold (vmatch_with_pair_proj (cbor_raw_match_fuel n pm) cbor_map_entry_value_proj entry (snd pair));
  unfold (cbor_map_entry_match (cbor_raw_match_fuel n) pm' entry pair');
  unfold (vmatch_pair_with_proj (cbor_raw_match_fuel n pm') cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel n pm') cbor_map_entry_value_proj) entry pair');
  unfold (vmatch_with_pair_proj (cbor_raw_match_fuel n pm') cbor_map_entry_value_proj entry (snd pair'));
  rewrite (cbor_raw_match_fuel n pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair))
       as (cbor_raw_match_fuel n pm entry.cbor_map_entry_key (fst pair));
  rewrite (cbor_raw_match_fuel n pm' (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair'))
       as (cbor_raw_match_fuel n pm' entry.cbor_map_entry_key (fst pair'));
  rewrite (cbor_raw_match_fuel n pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair))
       as (cbor_raw_match_fuel n pm entry.cbor_map_entry_value (snd pair));
  rewrite (cbor_raw_match_fuel n pm' (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair'))
       as (cbor_raw_match_fuel n pm' entry.cbor_map_entry_value (snd pair'));
  cbor_raw_match_fuel_gather n entry.cbor_map_entry_key
    #pm #(Ghost.hide (fst pair)) #pm' #(Ghost.hide (fst pair'));
  cbor_raw_match_fuel_gather n entry.cbor_map_entry_value
    #pm #(Ghost.hide (snd pair)) #pm' #(Ghost.hide (snd pair'));
  rewrite (cbor_raw_match_fuel n (pm +. pm') entry.cbor_map_entry_key (fst pair))
       as (cbor_raw_match_fuel n (pm +. pm') (cbor_map_entry_key_proj.pair_proj_get entry) (fst pair));
  rewrite (cbor_raw_match_fuel n (pm +. pm') entry.cbor_map_entry_value (snd pair))
       as (cbor_raw_match_fuel n (pm +. pm') (cbor_map_entry_value_proj.pair_proj_get entry) (snd pair));
  fold (vmatch_with_pair_proj (cbor_raw_match_fuel n (pm +. pm')) cbor_map_entry_value_proj entry (snd pair));
  fold (vmatch_pair_with_proj (cbor_raw_match_fuel n (pm +. pm')) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel n (pm +. pm')) cbor_map_entry_value_proj) entry pair);
  fold (cbor_map_entry_match (cbor_raw_match_fuel n) (pm +. pm') entry pair);
  fold (cbor_map_entry_vmatch_fuel n (pm +. pm') entry pair);
}

let cbor_map_entry_vmatch_fuel_share_t (n: nat) : I.share_t (cbor_map_entry_vmatch_fuel n) =
  cbor_map_entry_vmatch_fuel_share_wrapper n

let cbor_map_entry_vmatch_fuel_gather_t (n: nat) : I.gather_t (cbor_map_entry_vmatch_fuel n) =
  cbor_map_entry_vmatch_fuel_gather_wrapper n

#pop-options

// === Phase D: fuel-aware array compare via iterator_next_eos ===

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
fn compare_cbor_raw_fuel_array_case
  (f64: squash SZ.fits_u64)
  (n: nat { n >= 1 })
  (ih: compare_cbor_raw_fuel_t (n - 1))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (len: SZ.t)
  (_: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  ))
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (
    Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
    List.Tot.length (array_v (Ghost.reveal v1)) == SZ.v len /\
    List.Tot.length (array_v (Ghost.reveal v2)) == SZ.v len
  )
returns res: I16.t
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (same_sign (I16.v res) (cbor_compare_array_total (array_v (Ghost.reveal v1)) (array_v (Ghost.reveal v2))))
{

  // Unfold cbor_raw_match_fuel n on both sides to cbor_raw_match_aux
  cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
  cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
  rewrite (cbor_raw_match_fuel n pm1 x1 v1)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
  rewrite (cbor_raw_match_fuel n pm2 x2 v2)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);

  // --- Side 1: get array, build trade chain ending at cbor_raw_match_fuel n ---
  let ar_ml1 = cbor_raw_get_array_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
  with pm1_a ar1 . assert (
    I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1_a ar_ml1 ar1 **
    trade (I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1_a ar_ml1 ar1)
          (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
  );
  // Build trade: cbor_raw_match_aux → cbor_raw_match_fuel n
  intro
    (trade
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
      (cbor_raw_match_fuel n pm1 x1 v1))
    #emp
    fn _ {
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1)
    };
  Trade.trans
    (I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1_a ar_ml1 ar1)
    (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
    (cbor_raw_match_fuel n pm1 x1 v1);

  // --- Side 2: same as side 1 ---
  let ar_ml2 = cbor_raw_get_array_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
  with pm2_a ar2 . assert (
    I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2_a ar_ml2 ar2 **
    trade (I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2_a ar_ml2 ar2)
          (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
  );
  intro
    (trade
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
      (cbor_raw_match_fuel n pm2 x2 v2))
    #emp
    fn _ {
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2)
    };
  Trade.trans
    (I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2_a ar_ml2 ar2)
    (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
    (cbor_raw_match_fuel n pm2 x2 v2);

  // Start iterators
  let it1_init = I.iterator_start
    (cbor_raw_match_fuel (n - 1))
    parse_raw_data_item (jump_raw_data_item f64)
    pm1_a ar_ml1 ar1
    (cbor_raw_match_fuel_share_t (n - 1))
    (cbor_raw_match_fuel_gather_t (n - 1));
  Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);
  let it2_init = I.iterator_start
    (cbor_raw_match_fuel (n - 1))
    parse_raw_data_item (jump_raw_data_item f64)
    pm2_a ar_ml2 ar2
    (cbor_raw_match_fuel_share_t (n - 1))
    (cbor_raw_match_fuel_gather_t (n - 1));
  Trade.trans _ _ (cbor_raw_match_fuel n pm2 x2 v2);

  let mut r_it1 = it1_init;
  let mut r_it2 = it2_init;
  let mut r_acc : I16.t = 0s;
  let mut r_cnt = 0sz;

  while (
    let acc = !r_acc;
    let cnt = !r_cnt;
    (SZ.lt cnt len && acc = 0s)
  ) invariant exists* it1c it2c (acc_c: I16.t) cnt_c rem1 rem2 pm1c pm2c .
    R.pts_to r_it1 it1c **
    R.pts_to r_it2 it2c **
    R.pts_to r_acc acc_c **
    R.pts_to r_cnt cnt_c **
    I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1c it1c rem1 **
    I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2c it2c rem2 **
    trade (I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1c it1c rem1)
          (cbor_raw_match_fuel n pm1 x1 v1) **
    trade (I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2c it2c rem2)
          (cbor_raw_match_fuel n pm2 x2 v2) **
    pure (
      SZ.v cnt_c <= SZ.v len /\
      List.Tot.length rem1 == SZ.v len - SZ.v cnt_c /\
      List.Tot.length rem2 == SZ.v len - SZ.v cnt_c /\
      Ghost.reveal ar1 == array_v (Ghost.reveal v1) /\
      Ghost.reveal ar2 == array_v (Ghost.reveal v2) /\
      (I16.v acc_c == 0 ==>
        cbor_compare_array_total (Ghost.reveal ar1) (Ghost.reveal ar2) ==
        cbor_compare_array_total rem1 rem2) /\
      (I16.v acc_c <> 0 ==>
        same_sign (I16.v acc_c) (cbor_compare_array_total (Ghost.reveal ar1) (Ghost.reveal ar2)))
    )
  {
    let e1 = I.iterator_next_eos
      (cbor_raw_match_fuel (n - 1))
      parse_raw_data_item
      (jump_raw_data_item f64)
      _ r_it1 _ _
      (cbor_raw_match_fuel_share_t (n - 1))
      (cbor_raw_match_fuel_gather_t (n - 1));
    unfold (I.iterator_next_eos_post (cbor_raw_match_fuel (n - 1)) parse_raw_data_item _ r_it1 _ _ e1);
    with pmv1 hdv1 tl1 it1n pm1n . assert (
      I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv1 e1 hdv1 **
      R.pts_to r_it1 it1n **
      I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1n it1n tl1
    );
    Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);

    let e2 = I.iterator_next_eos
      (cbor_raw_match_fuel (n - 1))
      parse_raw_data_item
      (jump_raw_data_item f64)
      _ r_it2 _ _
      (cbor_raw_match_fuel_share_t (n - 1))
      (cbor_raw_match_fuel_gather_t (n - 1));
    unfold (I.iterator_next_eos_post (cbor_raw_match_fuel (n - 1)) parse_raw_data_item _ r_it2 _ _ e2);
    with pmv2 hdv2 tl2 it2n pm2n . assert (
      I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv2 e2 hdv2 **
      R.pts_to r_it2 it2n **
      I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2n it2n tl2
    );
    Trade.trans _ _ (cbor_raw_match_fuel n pm2 x2 v2);

    // 4-way dispatch via nested match (tail position; updates r_acc/r_cnt inside each branch)
    let old_cnt = !r_cnt;
    match e1 {
      EElement xx1 -> {
        rewrite (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv1 (EElement xx1) hdv1)
             as (cbor_raw_match_fuel (n - 1) pmv1 xx1 hdv1);
        match e2 {
          EElement xx2 -> {
            rewrite (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv2 (EElement xx2) hdv2)
                 as (cbor_raw_match_fuel (n - 1) pmv2 xx2 hdv2);
            let r2 = ih xx1 xx2 #pmv1 #hdv1 #pmv2 #hdv2;
            rewrite (cbor_raw_match_fuel (n - 1) pmv2 xx2 hdv2)
                 as (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv2 (EElement xx2) hdv2);
            rewrite (cbor_raw_match_fuel (n - 1) pmv1 xx1 hdv1)
                 as (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv1 (EElement xx1) hdv1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
            r_acc := r2;
            r_cnt := SZ.add old_cnt 1sz;
          }
          ESerialized s2 -> {
            rewrite (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv2 (ESerialized s2) hdv2)
                 as (PPB.pts_to_parsed parse_raw_data_item s2 #pmv2 hdv2);
            cbor_raw_match_fuel_implies_pos (n - 1) xx1 #pmv1 #hdv1;
            // Convert pts_to_parsed → strong_prefix at pmv2/2 + trade-back
            PPB.pts_to_parsed_weaken_strong_prefix parse_raw_data_item s2;
            // Read the cbor_raw from the strong_prefix slice
            let reader = cbor_raw_read_fuel (n - 1) (pmv2 /. 2.0R) f64;
            let xx2 = reader s2 #(pmv2 /. 2.0R) #hdv2;
            // Compose trades: cbor_raw_match_fuel (n - 1) (pmv2/2) → strong_prefix #(pmv2/2) → pts_to_parsed #pmv2
            Trade.trans
              (cbor_raw_match_fuel (n - 1) (pmv2 /. 2.0R) xx2 hdv2)
              (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #(pmv2 /. 2.0R) hdv2)
              (PPB.pts_to_parsed parse_raw_data_item s2 #pmv2 hdv2);
            let r2 = ih xx1 xx2 #pmv1 #hdv1 #(pmv2 /. 2.0R) #hdv2;
            Trade.elim
              (cbor_raw_match_fuel (n - 1) (pmv2 /. 2.0R) xx2 hdv2)
              (PPB.pts_to_parsed parse_raw_data_item s2 #pmv2 hdv2);
            rewrite (PPB.pts_to_parsed parse_raw_data_item s2 #pmv2 hdv2)
                 as (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv2 (ESerialized s2) hdv2);
            rewrite (cbor_raw_match_fuel (n - 1) pmv1 xx1 hdv1)
                 as (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv1 (EElement xx1) hdv1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
            r_acc := r2;
            r_cnt := SZ.add old_cnt 1sz;
          }
        }
      }
      ESerialized s1 -> {
        rewrite (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv1 (ESerialized s1) hdv1)
             as (PPB.pts_to_parsed parse_raw_data_item s1 #pmv1 hdv1);
        match e2 {
          EElement xx2 -> {
            rewrite (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv2 (EElement xx2) hdv2)
                 as (cbor_raw_match_fuel (n - 1) pmv2 xx2 hdv2);
            cbor_raw_match_fuel_implies_pos (n - 1) xx2 #pmv2 #hdv2;
            PPB.pts_to_parsed_weaken_strong_prefix parse_raw_data_item s1;
            let reader = cbor_raw_read_fuel (n - 1) (pmv1 /. 2.0R) f64;
            let xx1 = reader s1 #(pmv1 /. 2.0R) #hdv1;
            Trade.trans
              (cbor_raw_match_fuel (n - 1) (pmv1 /. 2.0R) xx1 hdv1)
              (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #(pmv1 /. 2.0R) hdv1)
              (PPB.pts_to_parsed parse_raw_data_item s1 #pmv1 hdv1);
            let r2 = ih xx1 xx2 #(pmv1 /. 2.0R) #hdv1 #pmv2 #hdv2;
            Trade.elim
              (cbor_raw_match_fuel (n - 1) (pmv1 /. 2.0R) xx1 hdv1)
              (PPB.pts_to_parsed parse_raw_data_item s1 #pmv1 hdv1);
            rewrite (cbor_raw_match_fuel (n - 1) pmv2 xx2 hdv2)
                 as (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv2 (EElement xx2) hdv2);
            rewrite (PPB.pts_to_parsed parse_raw_data_item s1 #pmv1 hdv1)
                 as (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv1 (ESerialized s1) hdv1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
            r_acc := r2;
            r_cnt := SZ.add old_cnt 1sz;
          }
          ESerialized s2 -> {
            rewrite (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv2 (ESerialized s2) hdv2)
                 as (PPB.pts_to_parsed parse_raw_data_item s2 #pmv2 hdv2);
            let r2 = byte_compare_pts_to_parsed_data_item s1 s2;
            rewrite (PPB.pts_to_parsed parse_raw_data_item s2 #pmv2 hdv2)
                 as (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv2 (ESerialized s2) hdv2);
            rewrite (PPB.pts_to_parsed parse_raw_data_item s1 #pmv1 hdv1)
                 as (I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv1 (ESerialized s1) hdv1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
            r_acc := r2;
            r_cnt := SZ.add old_cnt 1sz;
          }
        }
      }
    }
  };
  // After loop: trade back to cbor_raw_match_fuel n
  Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
  Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
  !r_acc
}

#pop-options

// === Phase E: fuel-aware map compare via iterator_next_eos ===

// E1: ghost helper to split a fuel map-entry vmatch into key + value matches.
ghost fn cbor_map_entry_vmatch_fuel_elim
  (m: nat)
  (entry: cbor_map_entry cbor_raw)
  (#pm: perm)
  (#pair: Ghost.erased (raw_data_item & raw_data_item))
requires cbor_map_entry_vmatch_fuel m pm entry pair
ensures
  cbor_raw_match_fuel m pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)) **
  cbor_raw_match_fuel m pm entry.cbor_map_entry_value (snd (Ghost.reveal pair))
{
  unfold (cbor_map_entry_vmatch_fuel m pm entry pair);
  unfold (cbor_map_entry_match (cbor_raw_match_fuel m) pm entry (Ghost.reveal pair));
  unfold (vmatch_pair_with_proj (cbor_raw_match_fuel m pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel m pm) cbor_map_entry_value_proj) entry (Ghost.reveal pair));
  unfold (vmatch_with_pair_proj (cbor_raw_match_fuel m pm) cbor_map_entry_value_proj entry (snd (Ghost.reveal pair)));
  rewrite (cbor_raw_match_fuel m pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst (Ghost.reveal pair)))
    as (cbor_raw_match_fuel m pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)));
  rewrite (cbor_raw_match_fuel m pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd (Ghost.reveal pair)))
    as (cbor_raw_match_fuel m pm entry.cbor_map_entry_value (snd (Ghost.reveal pair)));
}

// E2: ghost helper to fold back from key + value matches into a fuel map-entry vmatch.
ghost fn cbor_map_entry_vmatch_fuel_intro
  (m: nat)
  (entry: cbor_map_entry cbor_raw)
  (pm: perm)
  (pair: Ghost.erased (raw_data_item & raw_data_item))
requires
  cbor_raw_match_fuel m pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)) **
  cbor_raw_match_fuel m pm entry.cbor_map_entry_value (snd (Ghost.reveal pair))
ensures cbor_map_entry_vmatch_fuel m pm entry pair
{
  rewrite (cbor_raw_match_fuel m pm entry.cbor_map_entry_key (fst (Ghost.reveal pair)))
    as (cbor_raw_match_fuel m pm (cbor_map_entry_key_proj.pair_proj_get entry) (fst (Ghost.reveal pair)));
  rewrite (cbor_raw_match_fuel m pm entry.cbor_map_entry_value (snd (Ghost.reveal pair)))
    as (cbor_raw_match_fuel m pm (cbor_map_entry_value_proj.pair_proj_get entry) (snd (Ghost.reveal pair)));
  fold (vmatch_with_pair_proj (cbor_raw_match_fuel m pm) cbor_map_entry_value_proj entry (snd (Ghost.reveal pair)));
  fold (vmatch_pair_with_proj (cbor_raw_match_fuel m pm) cbor_map_entry_key_proj
    (vmatch_with_pair_proj (cbor_raw_match_fuel m pm) cbor_map_entry_value_proj) entry (Ghost.reveal pair));
  fold (cbor_map_entry_match (cbor_raw_match_fuel m) pm entry (Ghost.reveal pair));
  fold (cbor_map_entry_vmatch_fuel m pm entry pair);
}

// E3: byte-compare two cbor-pair data items represented as full pts_to_parsed slices.
// Used for the ESerialized/ESerialized case of a map iterator at fuel n-1.
// Mirrors byte_compare_pts_to_parsed_pair_data_item but with pts_to_parsed instead of
// pts_to_parsed_strong_prefix — iterator_next_eos's ESerialized yields the full parsed form.

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

inline_for_extraction
fn byte_compare_pts_to_parsed_pair_data_item_full
  (s1 s2: S.slice byte)
  (#p1: perm) (#kv1: Ghost.erased (raw_data_item & raw_data_item))
  (#p2: perm) (#kv2: Ghost.erased (raw_data_item & raw_data_item))
requires
  PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s1 #p1 kv1 **
  PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #p2 kv2
returns res: I16.t
ensures
  PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s1 #p1 kv1 **
  PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #p2 kv2 **
  pure (same_sign (I16.v res) (cbor_compare_pair kv1 kv2))
{
  SCE.pair_byte_compare_eq_cbor_compare_pair (Ghost.reveal kv1) (Ghost.reveal kv2);
  let pair_ser = serialize_nondep_then serialize_raw_data_item serialize_raw_data_item;
  PPB.pts_to_parsed_serialized pair_ser s1;
  PPB.pts_to_parsed_serialized pair_ser s2;
  unfold (LPS.pts_to_serialized pair_ser s1 #p1 (Ghost.reveal kv1));
  unfold (LPS.pts_to_serialized pair_ser s2 #p2 (Ghost.reveal kv2));
  let res = lex_compare_bytes s1 s2;
  fold (LPS.pts_to_serialized pair_ser s1 #p1 (Ghost.reveal kv1));
  fold (LPS.pts_to_serialized pair_ser s2 #p2 (Ghost.reveal kv2));
  Trade.elim (LPS.pts_to_serialized pair_ser s1 #p1 (Ghost.reveal kv1))
             (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s1 #p1 kv1);
  Trade.elim (LPS.pts_to_serialized pair_ser s2 #p2 (Ghost.reveal kv2))
             (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #p2 kv2);
  res
}

#pop-options

// E4: pair reader at fuel m. Mirrors NC.cbor_map_entry_zero_copy_parse but uses
// cbor_raw_read_fuel m pm0 instead of cbor_raw_read 1.0R, producing
// cbor_map_entry_vmatch_fuel m pm0 entry v in the postcondition.

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

inline_for_extraction
fn cbor_map_entry_zero_copy_parse_fuel
  (m: nat { m >= 1 })
  (pm0: perm)
  (f64: squash SZ.fits_u64)
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased (raw_data_item & raw_data_item))
requires PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v
returns res: cbor_map_entry cbor_raw
ensures cbor_map_entry_vmatch_fuel m pm0 res v **
        Trade.trade (cbor_map_entry_vmatch_fuel m pm0 res v)
                    (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v)
{
  let zcp1 = PPB.zero_copy_parse_of_strong_prefix (cbor_raw_read_fuel m pm0 f64) ();
  let pair = LowParse.PulseParse.Combinators.zero_copy_parse_nondep_then (jump_raw_data_item f64) zcp1 () zcp1 input;
  let entry : cbor_map_entry cbor_raw = { cbor_map_entry_key = fst pair; cbor_map_entry_value = snd pair };
  rewrite (vmatch_pair (cbor_raw_match_fuel m pm0) (cbor_raw_match_fuel m pm0) pair (Ghost.reveal v))
       as (cbor_map_entry_vmatch_fuel m pm0 entry v);
  rewrite (Trade.trade (vmatch_pair (cbor_raw_match_fuel m pm0) (cbor_raw_match_fuel m pm0) pair (Ghost.reveal v))
                       (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v))
       as (Trade.trade (cbor_map_entry_vmatch_fuel m pm0 entry v)
                       (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) input #pm v));
  entry
}

#pop-options

// E5: fuel-aware map compare case via iterator_next_eos. Mirrors Phase D
// (compare_cbor_raw_fuel_array_case) but each iterator yields a cbor_map_entry,
// and the per-element compare runs key-then-value via ih.

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
fn compare_cbor_raw_fuel_map_case
  (f64: squash SZ.fits_u64)
  (n: nat { n >= 1 })
  (ih: compare_cbor_raw_fuel_t (n - 1))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (len: SZ.t)
  (_: squash (
    CBOR_Case_Map? x1 /\ CBOR_Case_Map? x2 /\
    IT.mixed_list_length (CBOR_Case_Map?.v x1).cbor_map_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Map?.v x2).cbor_map_ptr == len
  ))
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (
    Map? (Ghost.reveal v1) /\ Map? (Ghost.reveal v2) /\
    List.Tot.length (map_v (Ghost.reveal v1)) == SZ.v len /\
    List.Tot.length (map_v (Ghost.reveal v2)) == SZ.v len
  )
returns res: I16.t
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (same_sign (I16.v res) (cbor_compare_map_total (map_v (Ghost.reveal v1)) (map_v (Ghost.reveal v2))))
{
  // Unfold cbor_raw_match_fuel n on both sides to cbor_raw_match_aux
  cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
  cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
  rewrite (cbor_raw_match_fuel n pm1 x1 v1)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
  rewrite (cbor_raw_match_fuel n pm2 x2 v2)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);

  // --- Side 1: get map, build trade chain ending at cbor_raw_match_fuel n ---
  let map_ml1 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
  with pm1_m map1_entries . assert (
    I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm1_m map_ml1 map1_entries **
    trade
      (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm1_m map_ml1 map1_entries)
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
  );
  // Switch from anonymous lambda to cbor_map_entry_vmatch_fuel (n - 1)
  rewrite
    (I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm1_m map_ml1 map1_entries)
    as
    (I.mixed_list_match
      (cbor_map_entry_vmatch_fuel (n - 1))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm1_m map_ml1 map1_entries);
  rewrite
    (trade
      (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm1_m map_ml1 map1_entries)
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1))
    as
    (trade
      (I.mixed_list_match
        (cbor_map_entry_vmatch_fuel (n - 1))
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm1_m map_ml1 map1_entries)
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1));
  // Build trade: cbor_raw_match_aux → cbor_raw_match_fuel n
  intro
    (trade
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
      (cbor_raw_match_fuel n pm1 x1 v1))
    #emp
    fn _ {
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1)
    };
  Trade.trans
    (I.mixed_list_match
      (cbor_map_entry_vmatch_fuel (n - 1))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm1_m map_ml1 map1_entries)
    (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
    (cbor_raw_match_fuel n pm1 x1 v1);

  // --- Side 2: same as side 1 ---
  let map_ml2 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
  with pm2_m map2_entries . assert (
    I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm2_m map_ml2 map2_entries **
    trade
      (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm2_m map_ml2 map2_entries)
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
  );
  rewrite
    (I.mixed_list_match
      (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
        cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v)
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm2_m map_ml2 map2_entries)
    as
    (I.mixed_list_match
      (cbor_map_entry_vmatch_fuel (n - 1))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm2_m map_ml2 map2_entries);
  rewrite
    (trade
      (I.mixed_list_match
        (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) ->
          cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v)
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm2_m map_ml2 map2_entries)
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2))
    as
    (trade
      (I.mixed_list_match
        (cbor_map_entry_vmatch_fuel (n - 1))
        (nondep_then parse_raw_data_item parse_raw_data_item)
        pm2_m map_ml2 map2_entries)
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2));
  intro
    (trade
      (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
      (cbor_raw_match_fuel n pm2 x2 v2))
    #emp
    fn _ {
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2)
    };
  Trade.trans
    (I.mixed_list_match
      (cbor_map_entry_vmatch_fuel (n - 1))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      pm2_m map_ml2 map2_entries)
    (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
    (cbor_raw_match_fuel n pm2 x2 v2);

  // Start iterators
  let it1_init = I.iterator_start
    (cbor_map_entry_vmatch_fuel (n - 1))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64))
    pm1_m map_ml1 map1_entries
    (cbor_map_entry_vmatch_fuel_share_t (n - 1))
    (cbor_map_entry_vmatch_fuel_gather_t (n - 1));
  Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);
  let it2_init = I.iterator_start
    (cbor_map_entry_vmatch_fuel (n - 1))
    (nondep_then parse_raw_data_item parse_raw_data_item)
    (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64))
    pm2_m map_ml2 map2_entries
    (cbor_map_entry_vmatch_fuel_share_t (n - 1))
    (cbor_map_entry_vmatch_fuel_gather_t (n - 1));
  Trade.trans _ _ (cbor_raw_match_fuel n pm2 x2 v2);

  let mut r_it1 = it1_init;
  let mut r_it2 = it2_init;
  let mut r_acc : I16.t = 0s;
  let mut r_cnt = 0sz;

  while (
    let acc = !r_acc;
    let cnt = !r_cnt;
    (SZ.lt cnt len && acc = 0s)
  ) invariant exists* it1c it2c (acc_c: I16.t) cnt_c rem1 rem2 pm1c pm2c .
    R.pts_to r_it1 it1c **
    R.pts_to r_it2 it2c **
    R.pts_to r_acc acc_c **
    R.pts_to r_cnt cnt_c **
    I.iterator_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1c it1c rem1 **
    I.iterator_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2c it2c rem2 **
    trade (I.iterator_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1c it1c rem1)
          (cbor_raw_match_fuel n pm1 x1 v1) **
    trade (I.iterator_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2c it2c rem2)
          (cbor_raw_match_fuel n pm2 x2 v2) **
    pure (
      SZ.v cnt_c <= SZ.v len /\
      List.Tot.length rem1 == SZ.v len - SZ.v cnt_c /\
      List.Tot.length rem2 == SZ.v len - SZ.v cnt_c /\
      Ghost.reveal map1_entries == map_v (Ghost.reveal v1) /\
      Ghost.reveal map2_entries == map_v (Ghost.reveal v2) /\
      (I16.v acc_c == 0 ==>
        cbor_compare_map_total (Ghost.reveal map1_entries) (Ghost.reveal map2_entries) ==
        cbor_compare_map_total rem1 rem2) /\
      (I16.v acc_c <> 0 ==>
        same_sign (I16.v acc_c) (cbor_compare_map_total (Ghost.reveal map1_entries) (Ghost.reveal map2_entries)))
    )
  {
    let e1 = I.iterator_next_eos
      (cbor_map_entry_vmatch_fuel (n - 1))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64))
      _ r_it1 _ _
      (cbor_map_entry_vmatch_fuel_share_t (n - 1))
      (cbor_map_entry_vmatch_fuel_gather_t (n - 1));
    unfold (I.iterator_next_eos_post (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) _ r_it1 _ _ e1);
    with pmv1 hdv1 tl1 it1n pm1n . assert (
      I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 e1 hdv1 **
      R.pts_to r_it1 it1n **
      I.iterator_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1n it1n tl1
    );
    Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);

    let e2 = I.iterator_next_eos
      (cbor_map_entry_vmatch_fuel (n - 1))
      (nondep_then parse_raw_data_item parse_raw_data_item)
      (jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64))
      _ r_it2 _ _
      (cbor_map_entry_vmatch_fuel_share_t (n - 1))
      (cbor_map_entry_vmatch_fuel_gather_t (n - 1));
    unfold (I.iterator_next_eos_post (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) _ r_it2 _ _ e2);
    with pmv2 hdv2 tl2 it2n pm2n . assert (
      I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 e2 hdv2 **
      R.pts_to r_it2 it2n **
      I.iterator_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2n it2n tl2
    );
    Trade.trans _ _ (cbor_raw_match_fuel n pm2 x2 v2);

    // 4-way dispatch via nested match (tail position; updates r_acc/r_cnt inside each branch)
    let old_cnt = !r_cnt;
    match e1 {
      EElement entry1 -> {
        rewrite (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 (EElement entry1) hdv1)
             as (cbor_map_entry_vmatch_fuel (n - 1) pmv1 entry1 hdv1);
        match e2 {
          EElement entry2 -> {
            rewrite (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (EElement entry2) hdv2)
                 as (cbor_map_entry_vmatch_fuel (n - 1) pmv2 entry2 hdv2);
            // Split each entry into key + value
            cbor_map_entry_vmatch_fuel_elim (n - 1) entry1 #pmv1 #hdv1;
            cbor_map_entry_vmatch_fuel_elim (n - 1) entry2 #pmv2 #hdv2;
            // Compare keys
            let ck = ih entry1.cbor_map_entry_key entry2.cbor_map_entry_key
                       #pmv1 #(Ghost.hide (fst (Ghost.reveal hdv1)))
                       #pmv2 #(Ghost.hide (fst (Ghost.reveal hdv2)));
            if (ck = 0s) {
              let cv = ih entry1.cbor_map_entry_value entry2.cbor_map_entry_value
                         #pmv1 #(Ghost.hide (snd (Ghost.reveal hdv1)))
                         #pmv2 #(Ghost.hide (snd (Ghost.reveal hdv2)));
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry1 pmv1 hdv1;
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry2 pmv2 hdv2;
              rewrite (cbor_map_entry_vmatch_fuel (n - 1) pmv1 entry1 hdv1)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 (EElement entry1) hdv1);
              rewrite (cbor_map_entry_vmatch_fuel (n - 1) pmv2 entry2 hdv2)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (EElement entry2) hdv2);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
              r_acc := cv;
              r_cnt := SZ.add old_cnt 1sz;
            } else {
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry1 pmv1 hdv1;
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry2 pmv2 hdv2;
              rewrite (cbor_map_entry_vmatch_fuel (n - 1) pmv1 entry1 hdv1)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 (EElement entry1) hdv1);
              rewrite (cbor_map_entry_vmatch_fuel (n - 1) pmv2 entry2 hdv2)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (EElement entry2) hdv2);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
              r_acc := ck;
              r_cnt := SZ.add old_cnt 1sz;
            };
          }
          ESerialized s2 -> {
            rewrite (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (ESerialized s2) hdv2)
                 as (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #pmv2 hdv2);
            // Derive fuel-positivity from entry1
            cbor_map_entry_vmatch_fuel_elim (n - 1) entry1 #pmv1 #hdv1;
            cbor_raw_match_fuel_implies_pos (n - 1) entry1.cbor_map_entry_key
              #pmv1 #(Ghost.hide (fst (Ghost.reveal hdv1)));
            cbor_map_entry_vmatch_fuel_intro (n - 1) entry1 pmv1 hdv1;
            // Read the pair from s2 at half permission
            let entry2 = cbor_map_entry_zero_copy_parse_fuel (n - 1) (pmv2 /. 2.0R) f64 s2 #pmv2 #hdv2;
            // Split entry1 and entry2 into key + value
            cbor_map_entry_vmatch_fuel_elim (n - 1) entry1 #pmv1 #hdv1;
            cbor_map_entry_vmatch_fuel_elim (n - 1) entry2 #(pmv2 /. 2.0R) #hdv2;
            let ck = ih entry1.cbor_map_entry_key entry2.cbor_map_entry_key
                       #pmv1 #(Ghost.hide (fst (Ghost.reveal hdv1)))
                       #(pmv2 /. 2.0R) #(Ghost.hide (fst (Ghost.reveal hdv2)));
            if (ck = 0s) {
              let cv = ih entry1.cbor_map_entry_value entry2.cbor_map_entry_value
                         #pmv1 #(Ghost.hide (snd (Ghost.reveal hdv1)))
                         #(pmv2 /. 2.0R) #(Ghost.hide (snd (Ghost.reveal hdv2)));
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry1 pmv1 hdv1;
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry2 (pmv2 /. 2.0R) hdv2;
              Trade.elim
                (cbor_map_entry_vmatch_fuel (n - 1) (pmv2 /. 2.0R) entry2 hdv2)
                (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #pmv2 hdv2);
              rewrite (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #pmv2 hdv2)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (ESerialized s2) hdv2);
              rewrite (cbor_map_entry_vmatch_fuel (n - 1) pmv1 entry1 hdv1)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 (EElement entry1) hdv1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
              r_acc := cv;
              r_cnt := SZ.add old_cnt 1sz;
            } else {
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry1 pmv1 hdv1;
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry2 (pmv2 /. 2.0R) hdv2;
              Trade.elim
                (cbor_map_entry_vmatch_fuel (n - 1) (pmv2 /. 2.0R) entry2 hdv2)
                (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #pmv2 hdv2);
              rewrite (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #pmv2 hdv2)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (ESerialized s2) hdv2);
              rewrite (cbor_map_entry_vmatch_fuel (n - 1) pmv1 entry1 hdv1)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 (EElement entry1) hdv1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
              r_acc := ck;
              r_cnt := SZ.add old_cnt 1sz;
            };
          }
        }
      }
      ESerialized s1 -> {
        rewrite (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 (ESerialized s1) hdv1)
             as (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s1 #pmv1 hdv1);
        match e2 {
          EElement entry2 -> {
            rewrite (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (EElement entry2) hdv2)
                 as (cbor_map_entry_vmatch_fuel (n - 1) pmv2 entry2 hdv2);
            // Derive fuel-positivity from entry2
            cbor_map_entry_vmatch_fuel_elim (n - 1) entry2 #pmv2 #hdv2;
            cbor_raw_match_fuel_implies_pos (n - 1) entry2.cbor_map_entry_key
              #pmv2 #(Ghost.hide (fst (Ghost.reveal hdv2)));
            cbor_map_entry_vmatch_fuel_intro (n - 1) entry2 pmv2 hdv2;
            // Read the pair from s1 at half permission
            let entry1 = cbor_map_entry_zero_copy_parse_fuel (n - 1) (pmv1 /. 2.0R) f64 s1 #pmv1 #hdv1;
            // Split entry1 and entry2 into key + value
            cbor_map_entry_vmatch_fuel_elim (n - 1) entry1 #(pmv1 /. 2.0R) #hdv1;
            cbor_map_entry_vmatch_fuel_elim (n - 1) entry2 #pmv2 #hdv2;
            let ck = ih entry1.cbor_map_entry_key entry2.cbor_map_entry_key
                       #(pmv1 /. 2.0R) #(Ghost.hide (fst (Ghost.reveal hdv1)))
                       #pmv2 #(Ghost.hide (fst (Ghost.reveal hdv2)));
            if (ck = 0s) {
              let cv = ih entry1.cbor_map_entry_value entry2.cbor_map_entry_value
                         #(pmv1 /. 2.0R) #(Ghost.hide (snd (Ghost.reveal hdv1)))
                         #pmv2 #(Ghost.hide (snd (Ghost.reveal hdv2)));
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry1 (pmv1 /. 2.0R) hdv1;
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry2 pmv2 hdv2;
              Trade.elim
                (cbor_map_entry_vmatch_fuel (n - 1) (pmv1 /. 2.0R) entry1 hdv1)
                (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s1 #pmv1 hdv1);
              rewrite (cbor_map_entry_vmatch_fuel (n - 1) pmv2 entry2 hdv2)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (EElement entry2) hdv2);
              rewrite (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s1 #pmv1 hdv1)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 (ESerialized s1) hdv1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
              r_acc := cv;
              r_cnt := SZ.add old_cnt 1sz;
            } else {
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry1 (pmv1 /. 2.0R) hdv1;
              cbor_map_entry_vmatch_fuel_intro (n - 1) entry2 pmv2 hdv2;
              Trade.elim
                (cbor_map_entry_vmatch_fuel (n - 1) (pmv1 /. 2.0R) entry1 hdv1)
                (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s1 #pmv1 hdv1);
              rewrite (cbor_map_entry_vmatch_fuel (n - 1) pmv2 entry2 hdv2)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (EElement entry2) hdv2);
              rewrite (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s1 #pmv1 hdv1)
                   as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 (ESerialized s1) hdv1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
              Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
              r_acc := ck;
              r_cnt := SZ.add old_cnt 1sz;
            };
          }
          ESerialized s2 -> {
            rewrite (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (ESerialized s2) hdv2)
                 as (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #pmv2 hdv2);
            let pair_res = byte_compare_pts_to_parsed_pair_data_item_full s1 s2;
            rewrite (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s2 #pmv2 hdv2)
                 as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv2 (ESerialized s2) hdv2);
            rewrite (PPB.pts_to_parsed (nondep_then parse_raw_data_item parse_raw_data_item) s1 #pmv1 hdv1)
                 as (I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 (ESerialized s1) hdv1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
            Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
            r_acc := pair_res;
            r_cnt := SZ.add old_cnt 1sz;
          }
        }
      }
    }
  };
  // After loop: trade back to cbor_raw_match_fuel n
  Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
  Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
  !r_acc
}

#pop-options

// === Final recursive entry point (placeholder during fuel refactor;
//     will be rewritten to wrap impl_cbor_compare_fuel) ===

fn impl_cbor_compare
  (f64: squash SZ.fits_u64)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2
returns res: I16.t
ensures
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (same_sign (I16.v res) (cbor_compare v1 v2))
{
  impl_cbor_compare_norec f64 x1 x2
}
