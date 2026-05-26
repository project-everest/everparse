module CBOR.Pulse.Raw.EverParse.Det.Compare.Dispatch
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.TaggedCase
include CBOR.Pulse.Raw.EverParse.Det.Compare.ArrayCase
include CBOR.Pulse.Raw.EverParse.Det.Compare.MapCase
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.Compare.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module I16 = FStar.Int16
module IT = LowParse.PulseParse.Iterator.Type

inline_for_extraction
val impl_cbor_compare_fuel_top
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat)
  (ih_tagged: compare_cbor_raw_fuel_tagged_local_t n)
  (ih_array: compare_cbor_raw_fuel_array_local_t n)
  (ih_map: compare_cbor_raw_fuel_map_local_t n)
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
