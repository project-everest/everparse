module CBOR.Pulse.Raw.EverParse.Nondet.Compare.ArrayCase
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.Base
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen

// Continuation type for the slow-path array comparison. Mirrors the
// caller-visible signature of compare_cbor_raw_array_case_fuel (same fuel n),
// but with the plain array precondition (no check_equiv == check_equiv_list
// requirement) and the check_equiv_array_total post-condition, so that the
// concrete slow knot member compare_cbor_raw_basic_fuel_array_slow can be
// substituted here as a direct call (no function pointer).
inline_for_extraction
noextract [@@noextract_to "krml"]
let compare_cbor_raw_array_slow_t
  (data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (map_bound: option nat)
  (n: Ghost.erased nat)
=
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (len: SZ.t) ->
  (sq: squash (
    CBOR_Case_Array? x1 /\ CBOR_Case_Array? x2 /\
    IT.mixed_list_length (CBOR_Case_Array?.v x1).cbor_array_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Array?.v x2).cbor_array_ptr == len)) ->
  (#pm1: perm) -> (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) -> (#v2: Ghost.erased raw_data_item) ->
  stt (option bool)
    (cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
     cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
     pure (
       Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
       List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
       List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
       raw_data_item_size v1 <= Ghost.reveal n /\
       raw_data_item_size v2 <= Ghost.reveal n))
    (fun res ->
       cbor_raw_match_fuel (Ghost.reveal n) pm1 x1 v1 **
       cbor_raw_match_fuel (Ghost.reveal n) pm2 x2 v2 **
       pure (res == check_equiv_array_total data_model map_bound (Ghost.reveal v1) (Ghost.reveal v2)))

// Always-slow array comparison entry: same signature as the original
// compare_cbor_raw_array_case_fuel (before the fast path was added). Runs the
// heavy IT.iterator (IBase|IPair) slow loop unconditionally. Extracted as its
// own C function, so it owns its stack frame.
inline_for_extraction
val compare_cbor_raw_array_slow_entry
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
: stt (option bool)
    (cbor_raw_match_fuel n pm1 x1 v1 **
     cbor_raw_match_fuel n pm2 x2 v2 **
     pure (
       Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
       List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
       List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
       raw_data_item_size v1 <= Ghost.reveal n /\
       raw_data_item_size v2 <= Ghost.reveal n /\
       check_equiv data_model (NG.option_sz_v map_bound) v1 v2 ==
         check_equiv_list (Array?.v (Ghost.reveal v1)) (Array?.v (Ghost.reveal v2)) (check_equiv_map data_model (NG.option_sz_v map_bound))
     ))
    (fun res ->
      cbor_raw_match_fuel n pm1 x1 v1 **
      cbor_raw_match_fuel n pm2 x2 v2 **
      pure (res == check_equiv data_model (NG.option_sz_v map_bound) v1 v2))

inline_for_extraction
val compare_cbor_raw_array_case_fuel
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (compare_rec: compare_cbor_raw_fuel_t data_model (NG.option_sz_v map_bound) (Ghost.hide (Ghost.reveal n - 1)))
  (slow_cont: compare_cbor_raw_array_slow_t data_model (NG.option_sz_v map_bound) n)
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
: stt (option bool)
    (cbor_raw_match_fuel n pm1 x1 v1 **
     cbor_raw_match_fuel n pm2 x2 v2 **
     pure (
       Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2) /\
       List.Tot.length (Array?.v (Ghost.reveal v1)) == SZ.v len /\
       List.Tot.length (Array?.v (Ghost.reveal v2)) == SZ.v len /\
       raw_data_item_size v1 <= Ghost.reveal n /\
       raw_data_item_size v2 <= Ghost.reveal n /\
       check_equiv data_model (NG.option_sz_v map_bound) v1 v2 ==
         check_equiv_list (Array?.v (Ghost.reveal v1)) (Array?.v (Ghost.reveal v2)) (check_equiv_map data_model (NG.option_sz_v map_bound))
     ))
    (fun res ->
      cbor_raw_match_fuel n pm1 x1 v1 **
      cbor_raw_match_fuel n pm2 x2 v2 **
      pure (res == check_equiv data_model (NG.option_sz_v map_bound) v1 v2))
