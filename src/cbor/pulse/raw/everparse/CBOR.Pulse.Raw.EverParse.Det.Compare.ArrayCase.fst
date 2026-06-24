module CBOR.Pulse.Raw.EverParse.Det.Compare.ArrayCase
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open CBOR.Pulse.Raw.Compare.Base
open CBOR.Pulse.Raw.Compare.Bytes
open LowParse.PulseParse.Iterator
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module I16 = FStar.Int16
module PPB = LowParse.PulseParse.Base

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_fuel_array_case
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (ih: compare_cbor_raw_fuel_t (Ghost.hide (Ghost.reveal n - 1)))
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

  // Start iterators (non-inline wrappers so iterator_start's working set
  // does not inflate this recursive function's stack frame)
  let it1_init = iterator_start_raw_data_item_fuel
    (Ghost.hide (Ghost.reveal n - 1)) pm1_a ar_ml1 ar1;
  Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);
  let it2_init = iterator_start_raw_data_item_fuel
    (Ghost.hide (Ghost.reveal n - 1)) pm2_a ar_ml2 ar2;
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
    let e1 = iterator_next_eos_raw_data_item_fuel_byref
      (Ghost.hide (Ghost.reveal n - 1)) _ r_it1 _ _;
    with pmv1 hdv1 tl1 it1n pm1n . assert (
      I.elt_or_serialized_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pmv1 e1 hdv1 **
      R.pts_to r_it1 it1n **
      I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1n it1n tl1
    );
    Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);

    let e2 = iterator_next_eos_raw_data_item_fuel_byref
      (Ghost.hide (Ghost.reveal n - 1)) _ r_it2 _ _;
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
            // (full application: avoid binding a partially-applied function value locally,
            //  which would survive KaRaMeL extraction and trigger Warning 16)
            let xx2 = cbor_raw_read_fuel (n - 1) (pmv2 /. 2.0R) f64 s2 #(pmv2 /. 2.0R) #hdv2;
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
            // Full application: avoid local binding of partial application.
            let xx1 = cbor_raw_read_fuel (n - 1) (pmv1 /. 2.0R) f64 s1 #(pmv1 /. 2.0R) #hdv1;
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
```

#pop-options
