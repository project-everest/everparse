module CBOR.Pulse.Raw.EverParse.Det.Compare
#lang-pulse
include CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
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
module U64 = FStar.UInt64
module I16 = FStar.Int16
module U8 = FStar.UInt8
module Spec = CBOR.Spec.Raw.Base
module NC = CBOR.Pulse.Raw.EverParse.Nondet.Compare

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
  | CBOR_Case_String v -> { size = v.cbor_string_size; value = U64.uint_to_t (SZ.v (S.len v.cbor_string_ptr)) }
  | _ -> { size = 0uy; value = 0UL }

let cbor_raw_string_len_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (NC.cbor_raw_match_fields_prop x v))
  (_: squash (String? v))
: Lemma (cbor_raw_string_len x == String?.len v)
= ()

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
  | CBOR_Case_Array v -> { size = v.cbor_array_length_size; value = U64.uint_to_t (SZ.v (I.mixed_list_length v.cbor_array_ptr)) }
  | _ -> { size = 0uy; value = 0UL }

let cbor_raw_array_raw_uint64_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (NC.cbor_raw_match_fields_prop x v))
  (_: squash (Array? v))
: Lemma (cbor_raw_array_raw_uint64 x == Array?.len v)
= ()

let cbor_raw_map_raw_uint64 (x: cbor_raw) : raw_uint64 =
  match x with
  | CBOR_Case_Map v -> { size = v.cbor_map_length_size; value = U64.uint_to_t (SZ.v (I.mixed_list_length v.cbor_map_ptr)) }
  | _ -> { size = 0uy; value = 0UL }

let cbor_raw_map_raw_uint64_eq
  (x: cbor_raw) (v: raw_data_item)
  (_: squash (NC.cbor_raw_match_fields_prop x v))
  (_: squash (Map? v))
: Lemma (cbor_raw_map_raw_uint64 x == Map?.len v)
= ()

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
    I.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    I.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
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
  let j = jump_raw_data_item f64;
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
  let it1_init = I.iterator_start cbor_raw_match parse_raw_data_item j pm1_a ar_ml1 ar1
    NC.cbor_raw_match_share_t NC.cbor_raw_match_gather_t;
  Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
  let it2_init = I.iterator_start cbor_raw_match parse_raw_data_item j pm2_a ar_ml2 ar2
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
    let e1 = I.iterator_next cbor_raw_match parse_raw_data_item j _ r_it1 _ _ NC.cbor_raw_match_share_t NC.cbor_raw_match_gather_t zcp;
    unfold (I.iterator_next_post cbor_raw_match parse_raw_data_item _ r_it1 _ _ e1);
    with pmv1 hdv1 tl1 it1n pm1n . assert (
      cbor_raw_match pmv1 e1 hdv1 **
      R.pts_to r_it1 it1n **
      I.iterator_match cbor_raw_match parse_raw_data_item pm1n it1n tl1
    );
    Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
    let e2 = I.iterator_next cbor_raw_match parse_raw_data_item j _ r_it2 _ _ NC.cbor_raw_match_share_t NC.cbor_raw_match_gather_t zcp;
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
    I.mixed_list_length (CBOR_Case_Map?.v x1).cbor_map_ptr == len /\
    I.mixed_list_length (CBOR_Case_Map?.v x2).cbor_map_ptr == len
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
  let j_pair = jump_nondep_then (jump_raw_data_item f64) (jump_raw_data_item f64);
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
  let it1_init = I.iterator_start NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) j_pair pm1_m map_ml1 map1_entries
    NC.cbor_map_entry_vmatch_share_wrapper NC.cbor_map_entry_vmatch_gather_wrapper;
  Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
  let it2_init = I.iterator_start NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) j_pair pm2_m map_ml2 map2_entries
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
    let e1 = I.iterator_next NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) j_pair _ r_it1 _ _ NC.cbor_map_entry_vmatch_share_wrapper NC.cbor_map_entry_vmatch_gather_wrapper zcp_pair;
    unfold (I.iterator_next_post NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) _ r_it1 _ _ e1);
    with pmv1 hdv1 tl1 it1n pm1n . assert (
      NC.cbor_map_entry_vmatch pmv1 e1 hdv1 **
      R.pts_to r_it1 it1n **
      I.iterator_match NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) pm1n it1n tl1
    );
    Trade.trans _ _ (cbor_raw_match pm1 x1 v1);
    let e2 = I.iterator_next NC.cbor_map_entry_vmatch (nondep_then parse_raw_data_item parse_raw_data_item) j_pair _ r_it2 _ _ NC.cbor_map_entry_vmatch_share_wrapper NC.cbor_map_entry_vmatch_gather_wrapper zcp_pair;
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

fn rec impl_cbor_compare
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
  cbor_compare_body f64 (impl_cbor_compare f64) x1 x2
}
