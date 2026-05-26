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

inline_for_extraction
val compare_cbor_raw_basic_dispatch_body
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (ih_tagged: compare_cbor_raw_basic_fuel_tagged_local_t n map_bound)
  (ih_array: compare_cbor_raw_basic_fuel_array_local_t n map_bound)
  (ih_map: compare_cbor_raw_basic_fuel_map_local_t n map_bound)
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: stt (option bool)
    (cbor_raw_match_fuel n pm1 x1 v1 **
     cbor_raw_match_fuel n pm2 x2 v2 **
     pure (raw_data_item_size v1 <= Ghost.reveal n /\
           raw_data_item_size v2 <= Ghost.reveal n))
    (fun res ->
      cbor_raw_match_fuel n pm1 x1 v1 **
      cbor_raw_match_fuel n pm2 x2 v2 **
      pure (res == check_equiv basic_data_model (NG.option_sz_v map_bound) v1 v2))

inline_for_extraction
val compare_cbor_raw_basic_fuel_top
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat)
  (ih_tagged: compare_cbor_raw_basic_fuel_tagged_local_t n map_bound)
  (ih_array: compare_cbor_raw_basic_fuel_array_local_t n map_bound)
  (ih_map: compare_cbor_raw_basic_fuel_map_local_t n map_bound)
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
