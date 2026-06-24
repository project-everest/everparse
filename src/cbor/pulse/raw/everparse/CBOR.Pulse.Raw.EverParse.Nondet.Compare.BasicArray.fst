module CBOR.Pulse.Raw.EverParse.Nondet.Compare.BasicArray
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.ArrayCase
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module IT = LowParse.PulseParse.Iterator.Type
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_basic_fuel_array_case
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (compare_rec: compare_cbor_raw_fuel_t basic_data_model (NG.option_sz_v map_bound) (Ghost.hide (Ghost.reveal n - 1)))
  (slow_cont: compare_cbor_raw_array_slow_t basic_data_model (NG.option_sz_v map_bound) n)
  (x1 x2: cbor_raw)
  (len: SZ.t)
  (sq: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  ))
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (
    Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
    List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
    List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
    raw_data_item_size v1 <= Ghost.reveal n /\
    raw_data_item_size v2 <= Ghost.reveal n
  )
returns res: option bool
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (res == check_equiv_array_total basic_data_model (NG.option_sz_v map_bound) v1 v2)
{
  check_equiv_array_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
  compare_cbor_raw_array_case_fuel f64 map_bound n compare_rec slow_cont x1 x2 len ()
}
```

inline_for_extraction
```pulse
fn compare_cbor_raw_basic_fuel_array_slow_case
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (compare_rec: compare_cbor_raw_fuel_t basic_data_model (NG.option_sz_v map_bound) (Ghost.hide (Ghost.reveal n - 1)))
  (x1 x2: cbor_raw)
  (len: SZ.t)
  (sq: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  ))
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (
    Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
    List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
    List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
    raw_data_item_size v1 <= Ghost.reveal n /\
    raw_data_item_size v2 <= Ghost.reveal n
  )
returns res: option bool
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (res == check_equiv_array_total basic_data_model (NG.option_sz_v map_bound) v1 v2)
{
  check_equiv_array_eq basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2) () ();
  compare_cbor_raw_array_slow_entry f64 map_bound n compare_rec x1 x2 len ()
}
```

#pop-options
