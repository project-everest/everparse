module CBOR.Pulse.Raw.EverParse.Nondet.Compare.Dispatch
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.BasicTagged
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.BasicArray
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.BasicMap
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module U64 = FStar.UInt64
module I16 = FStar.Int16
module IT = LowParse.PulseParse.Iterator.Type
module Spec = CBOR.Spec.API.Format
module CompareBytes = CBOR.Pulse.Raw.Compare.Bytes
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen

#push-options "--z3rlimit 512 --fuel 4 --ifuel 4 --split_queries always --ext no:context_pruning"

inline_for_extraction
```pulse
fn compare_cbor_raw_basic_dispatch_body
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (ih_tagged: compare_cbor_raw_basic_fuel_tagged_local_t n map_bound)
  (ih_array: compare_cbor_raw_basic_fuel_array_local_t n map_bound)
  (ih_map: compare_cbor_raw_basic_fuel_map_local_t n map_bound)
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (raw_data_item_size v1 <= Ghost.reveal n /\
        raw_data_item_size v2 <= Ghost.reveal n)
returns res: option bool
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (res == check_equiv basic_data_model (NG.option_sz_v map_bound) v1 v2)
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
  let mt1 = cbor_raw_get_major_type_aux (cbor_raw_match_fuel (n - 1)) pm1 x1;
  let mt2 = cbor_raw_get_major_type_aux (cbor_raw_match_fuel (n - 1)) pm2 x2;
  if (mt1 <> mt2) {
    check_equiv_mismatch_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    Some false
  } else if (mt1 = Spec.cbor_major_type_simple_value) {
    assert (pure (CBOR_Case_Simple? x1 /\ CBOR_Case_Simple? x2));
    let sv1 = CBOR_Case_Simple?.v x1;
    let sv2 = CBOR_Case_Simple?.v x2;
    let res = sv1 = sv2;
    check_equiv_simple_eq basic_data_model (NG.option_sz_v map_bound) sv1 sv2 ();
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    Some res
  } else if (mt1 = Spec.cbor_major_type_uint64 || mt1 = Spec.cbor_major_type_neg_int64) {
    assert (pure (Int64? (Ghost.reveal v1) /\ Int64? (Ghost.reveal v2)));
    assert (pure (CBOR_Case_Int? x1 /\ CBOR_Case_Int? x2));
    let vi1 = CBOR_Case_Int?.v x1;
    let vi2 = CBOR_Case_Int?.v x2;
    let res = vi1.cbor_int_type = vi2.cbor_int_type && (vi1.cbor_int_value <: U64.t) = (vi2.cbor_int_value <: U64.t);
    check_equiv_int_eq basic_data_model (NG.option_sz_v map_bound) vi1.cbor_int_type { size = vi1.cbor_int_size; value = vi1.cbor_int_value } vi2.cbor_int_type { size = vi2.cbor_int_size; value = vi2.cbor_int_value } ();
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    Some res
  } else if (mt1 = Spec.cbor_major_type_byte_string || mt1 = Spec.cbor_major_type_text_string) {
    assert (pure (String? (Ghost.reveal v1) /\ String? (Ghost.reveal v2)));
    assert (pure (CBOR_Case_String? x1 /\ CBOR_Case_String? x2));
    let vs1 = CBOR_Case_String?.v x1;
    let vs2 = CBOR_Case_String?.v x2;
    if (vs1.cbor_string_type <> vs2.cbor_string_type) {
      check_equiv_string_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1);
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2);
      Some false
    } else {
      let s1 = cbor_raw_get_string_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
      let s2 = cbor_raw_get_string_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
      let cmp = CompareBytes.lex_compare_bytes s1 s2;
      CBOR.Spec.Raw.Format.bytes_lex_compare_equal (String?.v (Ghost.reveal v1)) (String?.v (Ghost.reveal v2));
      check_equiv_string_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
      Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
      Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1);
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2);
      let res = cmp = 0s;
      Some res
    }
  } else if (mt1 = Spec.cbor_major_type_tagged) {
    check_equiv_tagged_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    ih_tagged () x1 x2 #pm1 #v1 #pm2 #v2
  } else if (mt1 = Spec.cbor_major_type_array) {
    check_equiv_array_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
    assert (pure (CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2));
    let len1 = IT.mixed_list_length (cbor_array_ptr_of x1);
    let len2 = IT.mixed_list_length (cbor_array_ptr_of x2);
    if (len1 <> len2) {
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1);
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2);
      Some false
    } else {
      cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
      cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
           as (cbor_raw_match_fuel n pm1 x1 v1);
      rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
           as (cbor_raw_match_fuel n pm2 x2 v2);
      ih_array () x1 x2 len1 () #pm1 #v1 #pm2 #v2
    }
  } else {
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    ih_map () x1 x2 #pm1 #v1 #pm2 #v2
  }
}
```

#pop-options

inline_for_extraction
```pulse
fn compare_cbor_raw_basic_fuel_top
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat)
  (ih_tagged: compare_cbor_raw_basic_fuel_tagged_local_t n map_bound)
  (ih_array: compare_cbor_raw_basic_fuel_array_local_t n map_bound)
  (ih_map: compare_cbor_raw_basic_fuel_map_local_t n map_bound)
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
  cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
  pure (raw_data_item_size v1 <= Ghost.reveal n /\
        raw_data_item_size v2 <= Ghost.reveal n)
returns res: option bool
ensures
  cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
  cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
  pure (res == check_equiv basic_data_model (NG.option_sz_v map_bound) v1 v2)
{
  cbor_raw_match_fuel_implies_pos (Ghost.reveal n) x1 #pm1 #v1;
  compare_cbor_raw_basic_dispatch_body f64 map_bound n ih_tagged ih_array ih_map x1 x2 #pm1 #v1 #pm2 #v2
}
```
