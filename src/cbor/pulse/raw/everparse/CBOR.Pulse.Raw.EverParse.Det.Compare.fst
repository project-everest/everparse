module CBOR.Pulse.Raw.EverParse.Det.Compare
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.Dispatch
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module I16 = FStar.Int16
module IT = LowParse.PulseParse.Iterator.Type

// F* mutual recursion: each wrapper extracts as a separate C function.

let rec impl_cbor_compare_fuel
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
: Tot
  (stt I16.t
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2)
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare v1 v2))))
  (decreases %[Ghost.reveal n; 1])
= impl_cbor_compare_fuel_top f64 n
    (impl_cbor_compare_fuel_tagged f64 n)
    (impl_cbor_compare_fuel_array f64 n)
    (impl_cbor_compare_fuel_map f64 n)
    x1 x2 #pm1 #v1 #pm2 #v2

and impl_cbor_compare_fuel_tagged
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat)
  (n_pos: squash (Ghost.reveal n >= 1))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
: Tot
  (stt I16.t
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (Tagged? (Ghost.reveal v1) /\ Tagged? (Ghost.reveal v2)))
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare_tagged_total (Ghost.reveal v1) (Ghost.reveal v2)))))
  (decreases %[Ghost.reveal n; 0])
= compare_cbor_raw_fuel_tagged_case f64 n
    (impl_cbor_compare_fuel f64 (Ghost.hide (Ghost.reveal n - 1)))
    x1 x2 #pm1 #v1 #pm2 #v2

and impl_cbor_compare_fuel_array
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat)
  (n_pos: squash (Ghost.reveal n >= 1))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (len: SZ.t)
  (sq: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len
  ))
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
: Tot
  (stt I16.t
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
      pure (same_sign (I16.v res) (cbor_compare_array_total (array_v (Ghost.reveal v1)) (array_v (Ghost.reveal v2))))))
  (decreases %[Ghost.reveal n; 0])
= compare_cbor_raw_fuel_array_case f64 n
    (impl_cbor_compare_fuel f64 (Ghost.hide (Ghost.reveal n - 1)))
    x1 x2 len sq #pm1 #v1 #pm2 #v2

and impl_cbor_compare_fuel_map
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat)
  (n_pos: squash (Ghost.reveal n >= 1))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (len: SZ.t)
  (sq: squash (
    CBOR_Case_Map? x1 /\ CBOR_Case_Map? x2 /\
    IT.mixed_list_length (CBOR_Case_Map?.v x1).cbor_map_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Map?.v x2).cbor_map_ptr == len
  ))
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
: Tot
  (stt I16.t
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
      pure (same_sign (I16.v res) (cbor_compare_map_total (map_v (Ghost.reveal v1)) (map_v (Ghost.reveal v2))))))
  (decreases %[Ghost.reveal n; 0])
= compare_cbor_raw_fuel_map_case f64 n
    (impl_cbor_compare_fuel f64 (Ghost.hide (Ghost.reveal n - 1)))
    x1 x2 len sq #pm1 #v1 #pm2 #v2

// Non-recursive F* `let` wrapper around the F* `let rec` `impl_cbor_compare_fuel`.
// Pulse's `is_stateful_application` can recognize non-rec F* lets returning stt
// (as it does for FStar.Pulse-like stt helpers e.g. Quicksort.Base.op_Array_Access)
// but cannot recognize recursive lets. This wrapper exposes the recursion as a
// callable stt value for Phase G.

let impl_cbor_compare_fuel_call
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
: stt I16.t
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2)
    (fun res ->
      cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
      cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare v1 v2)))
= impl_cbor_compare_fuel f64 n x1 x2 #pm1 #v1 #pm2 #v2

// === Phase G: final wrapper using cbor_raw_match_to_fuel ===

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
  let n1 = cbor_raw_match_to_fuel x1;
  let n2 = cbor_raw_match_to_fuel x2;
  let n : Ghost.erased nat = Ghost.hide (nat_max (Ghost.reveal n1) (Ghost.reveal n2));
  cbor_raw_match_fuel_weaken (Ghost.reveal n1) (Ghost.reveal n) x1;
  cbor_raw_match_fuel_weaken (Ghost.reveal n2) (Ghost.reveal n) x2;
  let res = impl_cbor_compare_fuel_call f64 n x1 x2 #pm1 #v1 #pm2 #v2;
  cbor_raw_match_of_fuel (Ghost.reveal n) x1;
  cbor_raw_match_of_fuel (Ghost.reveal n) x2;
  res
}
