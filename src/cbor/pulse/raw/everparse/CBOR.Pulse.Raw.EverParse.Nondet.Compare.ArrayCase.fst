module CBOR.Pulse.Raw.EverParse.Nondet.Compare.ArrayCase
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.Base
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open LowParse.Spec.Combinators
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen

#push-options "--z3rlimit 512 --fuel 4 --ifuel 4 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_array_case_fuel
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (compare_rec: compare_cbor_raw_fuel_t data_model (NG.option_sz_v map_bound) (Ghost.hide (Ghost.reveal n - 1)))
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
    List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
    List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
    raw_data_item_size v1 <= Ghost.reveal n /\
    raw_data_item_size v2 <= Ghost.reveal n /\
    check_equiv data_model (NG.option_sz_v map_bound) v1 v2 ==
      check_equiv_list (Array?.v (Ghost.reveal v1)) (Array?.v (Ghost.reveal v2)) (check_equiv_map data_model (NG.option_sz_v map_bound))
  )
returns res: option bool
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (res == check_equiv data_model (NG.option_sz_v map_bound) v1 v2)
{
  if (len = 0sz) {
    Some true
  } else {
    raw_data_item_size_eq v1;
    raw_data_item_size_eq v2;
    let n1 : Ghost.erased nat = Ghost.hide (Ghost.reveal n - 1);
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_fuel n pm1 x1 v1)
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
    rewrite (cbor_raw_match_fuel n pm2 x2 v2)
         as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);

    let ar_ml1 = cbor_raw_get_array_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
    with pm1_a ar1 . assert (
      I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1_a ar_ml1 ar1 **
      trade (I.mixed_list_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1_a ar_ml1 ar1)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
    );
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

    let it1_init = I.iterator_start
      (cbor_raw_match_fuel (n - 1))
      parse_raw_data_item jump_raw_data_item_eta
      pm1_a ar_ml1 ar1
      (cbor_raw_match_fuel_share_t (n - 1))
      (cbor_raw_match_fuel_gather_t (n - 1));
    Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);
    let it2_init = I.iterator_start
      (cbor_raw_match_fuel (n - 1))
      parse_raw_data_item jump_raw_data_item_eta
      pm2_a ar_ml2 ar2
      (cbor_raw_match_fuel_share_t (n - 1))
      (cbor_raw_match_fuel_gather_t (n - 1));
    Trade.trans _ _ (cbor_raw_match_fuel n pm2 x2 v2);

    let mut r_it1 = it1_init;
    let mut r_it2 = it2_init;
    let mut r_acc : option bool = Some true;
    let mut r_cnt = 0sz;

    while (
      let acc = !r_acc;
      let cnt = !r_cnt;
      (SZ.lt cnt len && acc = Some true)
    ) invariant exists* it1c it2c acc_c cnt_c rem1 rem2 pm1c pm2c .
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
        Ghost.reveal ar1 == Array?.v (Ghost.reveal v1) /\
        Ghost.reveal ar2 == Array?.v (Ghost.reveal v2) /\
        list_sum raw_data_item_size rem1 <= list_sum raw_data_item_size (Ghost.reveal ar1) /\
        list_sum raw_data_item_size rem2 <= list_sum raw_data_item_size (Ghost.reveal ar2) /\
        list_sum raw_data_item_size rem1 + list_sum raw_data_item_size rem2 <= list_sum raw_data_item_size (Ghost.reveal ar1) + list_sum raw_data_item_size (Ghost.reveal ar2) /\
        check_equiv_list (Ghost.reveal ar1) (Ghost.reveal ar2) (check_equiv_map data_model (NG.option_sz_v map_bound)) ==
          option_and acc_c (check_equiv_list rem1 rem2 (check_equiv_map data_model (NG.option_sz_v map_bound)))
      )
    {
      let it1_cur = !r_it1;
      let e1, it1n = iterator_next_raw_data_item_fuel (Ghost.hide (Ghost.reveal n - 1)) f64 _ it1_cur _;
      r_it1 := it1n;
      with pmv1 hdv1 tl1 pm1n . assert (
        cbor_raw_match_fuel (n - 1) pmv1 e1 hdv1 **
        R.pts_to r_it1 it1n **
        I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm1n it1n tl1
      );
      Trade.trans _ _ (cbor_raw_match_fuel n pm1 x1 v1);
      let it2_cur = !r_it2;
      let e2, it2n = iterator_next_raw_data_item_fuel (Ghost.hide (Ghost.reveal n - 1)) f64 _ it2_cur _;
      r_it2 := it2n;
      with pmv2 hdv2 tl2 pm2n . assert (
        cbor_raw_match_fuel (n - 1) pmv2 e2 hdv2 **
        R.pts_to r_it2 it2n **
        I.iterator_match (cbor_raw_match_fuel (n - 1)) parse_raw_data_item pm2n it2n tl2
      );
      Trade.trans _ _ (cbor_raw_match_fuel n pm2 x2 v2);
      let pair_res = compare_rec e1 e2;
      Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm1 x1 v1);
      Trade.elim_hyp_l _ _ (cbor_raw_match_fuel n pm2 x2 v2);
      let old_acc = !r_acc;
      let old_cnt = !r_cnt;
      r_acc := option_and old_acc pair_res;
      r_cnt := SZ.add old_cnt 1sz;
      check_equiv_list_cons (Ghost.reveal hdv1) (Ghost.reveal hdv2) (Ghost.reveal tl1) (Ghost.reveal tl2)
        (list_sum raw_data_item_size (Ghost.reveal ar1) + list_sum raw_data_item_size (Ghost.reveal ar2))
        (check_equiv_map data_model (NG.option_sz_v map_bound)) ();
      check_equiv_eq data_model (NG.option_sz_v map_bound) (Ghost.reveal hdv1) (Ghost.reveal hdv2);
      option_and_assoc old_acc pair_res
        (check_equiv_list (Ghost.reveal tl1) (Ghost.reveal tl2) (check_equiv_map data_model (NG.option_sz_v map_bound)));
    };
    Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
    Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
    !r_acc
  }
}
```

#pop-options
