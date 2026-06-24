module CBOR.Pulse.Raw.EverParse.Nondet.Compare
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.Dispatch
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module IT = LowParse.PulseParse.Iterator.Type
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen

// === F* mutual recursion ===

let rec compare_cbor_raw_basic_fuel
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat)
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: Tot
    (stt (option bool)
      (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
       cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
       pure (raw_data_item_size v1 <= Ghost.reveal n /\
             raw_data_item_size v2 <= Ghost.reveal n))
      (fun res ->
        cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
        cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
        pure (res == check_equiv basic_data_model (NG.option_sz_v map_bound) v1 v2)))
    (decreases %[Ghost.reveal n; 2])
= compare_cbor_raw_basic_fuel_top f64 map_bound n
    (compare_cbor_raw_basic_fuel_tagged f64 map_bound n)
    (compare_cbor_raw_basic_fuel_array f64 map_bound n)
    (compare_cbor_raw_basic_fuel_map f64 map_bound n)
    x1 x2 #pm1 #v1 #pm2 #v2

and compare_cbor_raw_basic_fuel_tagged
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat)
  (n_pos: squash (Ghost.reveal n >= 1))
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: Tot
    (stt (option bool)
      (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
       cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
       pure (Tagged? (Ghost.reveal v1) /\ Tagged? (Ghost.reveal v2) /\
             raw_data_item_size v1 <= Ghost.reveal n /\
             raw_data_item_size v2 <= Ghost.reveal n))
      (fun res ->
        cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
        cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
        pure (res == check_equiv_tagged_total basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2))))
    (decreases %[Ghost.reveal n; 0])
= compare_cbor_raw_basic_fuel_tagged_case f64 map_bound n
    (compare_cbor_raw_basic_fuel f64 map_bound (Ghost.hide (Ghost.reveal n - 1)))
    x1 x2 #pm1 #v1 #pm2 #v2

and compare_cbor_raw_basic_fuel_array
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat)
  (n_pos: squash (Ghost.reveal n >= 1))
  (x1 x2: cbor_raw)
  (len: SZ.t)
  (sq: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  ))
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: Tot
    (stt (option bool)
      (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
       cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
       pure (
         Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
         List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
         List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
         raw_data_item_size v1 <= Ghost.reveal n /\
         raw_data_item_size v2 <= Ghost.reveal n
       ))
      (fun res ->
        cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
        cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
        pure (res == check_equiv_array_total basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2))))
    (decreases %[Ghost.reveal n; 1])
= compare_cbor_raw_basic_fuel_array_case f64 map_bound n
    (compare_cbor_raw_basic_fuel f64 map_bound (Ghost.hide (Ghost.reveal n - 1)))
    (compare_cbor_raw_basic_fuel_array_slow f64 map_bound n n_pos)
    x1 x2 len sq #pm1 #v1 #pm2 #v2

and compare_cbor_raw_basic_fuel_array_slow
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat)
  (n_pos: squash (Ghost.reveal n >= 1))
  (x1 x2: cbor_raw)
  (len: SZ.t)
  (sq: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  ))
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: Tot
    (stt (option bool)
      (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
       cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
       pure (
         Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
         List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
         List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
         raw_data_item_size v1 <= Ghost.reveal n /\
         raw_data_item_size v2 <= Ghost.reveal n
       ))
      (fun res ->
        cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
        cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
        pure (res == check_equiv_array_total basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2))))
    (decreases %[Ghost.reveal n; 0])
= compare_cbor_raw_basic_fuel_array_slow_case f64 map_bound n
    (compare_cbor_raw_basic_fuel f64 map_bound (Ghost.hide (Ghost.reveal n - 1)))
    x1 x2 len sq #pm1 #v1 #pm2 #v2

and compare_cbor_raw_basic_fuel_map
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat)
  (n_pos: squash (Ghost.reveal n >= 1))
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: Tot
    (stt (option bool)
      (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
       cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
       pure (Map? (Ghost.reveal v1) /\ Map? (Ghost.reveal v2) /\
             raw_data_item_size v1 <= Ghost.reveal n /\
             raw_data_item_size v2 <= Ghost.reveal n))
      (fun res ->
        cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
        cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
        pure (res == check_equiv_map_total basic_data_model (NG.option_sz_v map_bound) (Ghost.reveal v1) (Ghost.reveal v2))))
    (decreases %[Ghost.reveal n; 0])
= let _ : squash (NG.option_sz_v (option_sz_decrement_safe map_bound) == option_nat_decrement_safe (NG.option_sz_v map_bound))
    = option_sz_decrement_safe_v map_bound in
  compare_cbor_raw_basic_fuel_map_case f64 map_bound n
    (compare_cbor_raw_basic_fuel f64 (option_sz_decrement_safe map_bound) (Ghost.hide (Ghost.reveal n - 1)))
    x1 x2 #pm1 #v1 #pm2 #v2

// Non-recursive F* `let` wrapper around the F* `let rec` `compare_cbor_raw_basic_fuel`.
// Pulse's `is_stateful_application` does not recognize recursive F* lets returning stt
// directly. This wrapper exposes the recursion as a callable stt value for Phase 7.

inline_for_extraction
let compare_cbor_raw_basic_fuel_call
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat)
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: stt (option bool)
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (raw_data_item_size v1 <= Ghost.reveal n /\
           raw_data_item_size v2 <= Ghost.reveal n))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (res == check_equiv basic_data_model (NG.option_sz_v map_bound) v1 v2))
= compare_cbor_raw_basic_fuel f64 map_bound n x1 x2 #pm1 #v1 #pm2 #v2

// === Phase 7: non-fuel wrapper using cbor_raw_match_to_fuel ===

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"

inline_for_extraction
```pulse
fn compare_cbor_raw_basic
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2
returns res: option bool
ensures
  cbor_raw_match pm1 x1 v1 **
  cbor_raw_match pm2 x2 v2 **
  pure (res == check_equiv basic_data_model (NG.option_sz_v map_bound) v1 v2)
{
  let n1 = cbor_raw_match_to_fuel x1 #pm1 #v1;
  let n2 = cbor_raw_match_to_fuel x2 #pm2 #v2;
  let n : Ghost.erased nat = Ghost.hide (
    nat_max
      (nat_max (Ghost.reveal n1) (Ghost.reveal n2))
      (nat_max (raw_data_item_size v1) (raw_data_item_size v2))
  );
  cbor_raw_match_fuel_weaken (Ghost.reveal n1) (Ghost.reveal n) x1 #pm1 #v1;
  cbor_raw_match_fuel_weaken (Ghost.reveal n2) (Ghost.reveal n) x2 #pm2 #v2;
  let res = compare_cbor_raw_basic_fuel_call f64 map_bound n x1 x2 #pm1 #v1 #pm2 #v2;
  cbor_raw_match_of_fuel (Ghost.reveal n) x1 #pm1 #v1;
  cbor_raw_match_of_fuel (Ghost.reveal n) x2 #pm2 #v2;
  res
}
```

#pop-options
