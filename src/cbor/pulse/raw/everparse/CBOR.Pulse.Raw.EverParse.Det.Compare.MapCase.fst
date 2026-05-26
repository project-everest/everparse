module CBOR.Pulse.Raw.EverParse.Det.Compare.MapCase
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open LowParse.PulseParse.Iterator
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open CBOR.Pulse.Raw.Compare.Bytes
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module I16 = FStar.Int16
module LPS = LowParse.Pulse.Base
module SCE = CBOR.Pulse.Raw.EverParse.SerializeCborEq

// Byte-compare two cbor-pair data items represented as full pts_to_parsed slices.
// Used for the ESerialized/ESerialized case of a map iterator at fuel n-1.
// Mirrors byte_compare_pts_to_parsed_pair_data_item but with pts_to_parsed instead of
// pts_to_parsed_strong_prefix — iterator_next_eos's ESerialized yields the full parsed form.

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

inline_for_extraction
```pulse
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
```

#pop-options

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_fuel_map_case
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (ih: compare_cbor_raw_fuel_t (Ghost.hide (Ghost.reveal n - 1)))
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

  // Start iterators (non-inline wrappers)
  let it1_init = iterator_start_map_entry_raw_data_item_fuel
    (Ghost.hide (Ghost.reveal n - 1)) pm1_m map_ml1 map1_entries;
  Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);
  let it2_init = iterator_start_map_entry_raw_data_item_fuel
    (Ghost.hide (Ghost.reveal n - 1)) pm2_m map_ml2 map2_entries;
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
    let e1 = iterator_next_eos_map_entry_raw_data_item_fuel_byref
      (Ghost.hide (Ghost.reveal n - 1)) _ r_it1 _ _;
    with pmv1 hdv1 tl1 it1n pm1n . assert (
      I.elt_or_serialized_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pmv1 e1 hdv1 **
      R.pts_to r_it1 it1n **
      I.iterator_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1n it1n tl1
    );
    Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);

    let e2 = iterator_next_eos_map_entry_raw_data_item_fuel_byref
      (Ghost.hide (Ghost.reveal n - 1)) _ r_it2 _ _;
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
```

#pop-options
