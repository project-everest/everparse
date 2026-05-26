module CBOR.Pulse.Raw.EverParse.Nondet.Compare.BasicMap
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.ListForAll
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open LowParse.Spec.Combinators
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen

#push-options "--z3rlimit 512 --fuel 4 --ifuel 4 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_basic_fuel_map_case
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (compare_rec_map: compare_cbor_raw_fuel_t basic_data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)) (Ghost.hide (Ghost.reveal n - 1)))
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (Map? (Ghost.reveal v1) /\ Map? (Ghost.reveal v2) /\
        raw_data_item_size v1 <= Ghost.reveal n /\
        raw_data_item_size v2 <= Ghost.reveal n)
returns res: option bool
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (res == check_equiv_map_total basic_data_model (NG.option_sz_v map_bound) v1 v2)
{
  cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
  cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
  rewrite (cbor_raw_match_fuel n pm1 x1 v1)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
  rewrite (cbor_raw_match_fuel n pm2 x2 v2)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
  raw_data_item_size_eq v1;
  raw_data_item_size_eq v2;
  cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm1 x1;
  cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm2 x2;
  cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm1 x1;
  cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm2 x2;
  check_equiv_map_map_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
  match map_bound {
    Some mb_v -> {
      if (mb_v = 0sz) {
        cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
        cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
             as (cbor_raw_match_fuel n pm1 x1 v1);
        rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
             as (cbor_raw_match_fuel n pm2 x2 v2);
        None #bool
      } else {
        option_nat_decrement_safe_spec (NG.option_sz_v map_bound);
        let map_ml1 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
        with pm1_m map1_entries . assert (
          I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries **
          Trade.trade
            (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
        );
        rewrite
          (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
          as (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries);
        rewrite
          (Trade.trade
            (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1))
          as (Trade.trade
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1));
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
          (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
          (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
          (cbor_raw_match_fuel n pm1 x1 v1);
        let map_ml2 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
        with pm2_m map2_entries . assert (
          I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries **
          Trade.trade
            (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
        );
        rewrite
          (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
          as (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries);
        rewrite
          (Trade.trade
            (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
            (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2))
          as (Trade.trade
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
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
          (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
          (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
          (cbor_raw_match_fuel n pm2 x2 v2);
        let fwd = compare_cbor_raw_list_for_all_fuel (Ghost.hide (Ghost.reveal n - 1))
                    #(check_equiv basic_data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)))
                    compare_rec_map f64
                    map_ml2 map_ml1;
        check_equiv_map_list_for_all_ext basic_data_model (option_nat_decrement_safe (NG.option_sz_v map_bound))
          (list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v1)) + list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v2)))
          (Ghost.reveal map2_entries) (Ghost.reveal map1_entries);
        match fwd {
          Some fwd_b -> {
            if fwd_b {
              let bwd = compare_cbor_raw_list_for_all_fuel (Ghost.hide (Ghost.reveal n - 1))
                          #(check_equiv basic_data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)))
                          compare_rec_map f64
                          map_ml1 map_ml2;
              check_equiv_map_list_for_all_ext basic_data_model (option_nat_decrement_safe (NG.option_sz_v map_bound))
                (list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v1)) + list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v2)))
                (Ghost.reveal map1_entries) (Ghost.reveal map2_entries);
              Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
              Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
              check_equiv_map_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
              bwd
            } else {
              Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
              Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
              check_equiv_map_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
              Some false
            }
          }
          None -> {
            Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
            Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
            check_equiv_map_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
            None #bool
          }
        }
      }
    }
    None -> {
      option_nat_decrement_safe_spec (NG.option_sz_v map_bound);
      let map_ml1 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
      with pm1_m map1_entries . assert (
        I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries **
        Trade.trade
          (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
          (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
      );
      rewrite
        (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
        as (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries);
      rewrite
        (Trade.trade
          (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
          (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1))
        as (Trade.trade
          (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
          (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1));
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
        (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm1_m map_ml1 map1_entries)
        (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
        (cbor_raw_match_fuel n pm1 x1 v1);
      let map_ml2 = cbor_raw_get_map_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
      with pm2_m map2_entries . assert (
        I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries **
        Trade.trade
          (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
          (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
      );
      rewrite
        (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
        as (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries);
      rewrite
        (Trade.trade
          (I.mixed_list_match (fun (pm0: perm) (elem: cbor_map_entry cbor_raw) (v: (raw_data_item & raw_data_item)) -> cbor_map_entry_match (cbor_raw_match_fuel (n - 1)) pm0 elem v) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
          (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2))
        as (Trade.trade
          (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
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
        (I.mixed_list_match (cbor_map_entry_vmatch_fuel (n - 1)) (nondep_then parse_raw_data_item parse_raw_data_item) pm2_m map_ml2 map2_entries)
        (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
        (cbor_raw_match_fuel n pm2 x2 v2);
      let fwd = compare_cbor_raw_list_for_all_fuel (Ghost.hide (Ghost.reveal n - 1))
                  #(check_equiv basic_data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)))
                  compare_rec_map f64
                  map_ml2 map_ml1;
      check_equiv_map_list_for_all_ext basic_data_model (option_nat_decrement_safe (NG.option_sz_v map_bound))
        (list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v1)) + list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v2)))
        (Ghost.reveal map2_entries) (Ghost.reveal map1_entries);
      match fwd {
        Some fwd_b -> {
          if fwd_b {
            let bwd = compare_cbor_raw_list_for_all_fuel (Ghost.hide (Ghost.reveal n - 1))
                        #(check_equiv basic_data_model (option_nat_decrement_safe (NG.option_sz_v map_bound)))
                        compare_rec_map f64
                        map_ml1 map_ml2;
            check_equiv_map_list_for_all_ext basic_data_model (option_nat_decrement_safe (NG.option_sz_v map_bound))
              (list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v1)) + list_sum (pair_sum raw_data_item_size raw_data_item_size) (Map?.v (Ghost.reveal v2)))
              (Ghost.reveal map1_entries) (Ghost.reveal map2_entries);
            Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
            Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
            check_equiv_map_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
            bwd
          } else {
            Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
            Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
            check_equiv_map_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
            Some false
          }
        }
        None -> {
          Trade.elim _ (cbor_raw_match_fuel n pm1 x1 v1);
          Trade.elim _ (cbor_raw_match_fuel n pm2 x2 v2);
          check_equiv_map_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2);
          None #bool
        }
      }
    }
  }
}
```

#pop-options
