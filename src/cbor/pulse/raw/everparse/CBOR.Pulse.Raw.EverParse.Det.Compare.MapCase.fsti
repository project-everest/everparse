module CBOR.Pulse.Raw.EverParse.Det.Compare.MapCase
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.Compare.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module I16 = FStar.Int16
module IT = LowParse.PulseParse.Iterator.Type

inline_for_extraction
val compare_cbor_raw_fuel_map_case
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (ih: compare_cbor_raw_fuel_t (Ghost.hide (Ghost.reveal n - 1)))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (len: SZ.t)
  (_: squash (
    CBOR_Case_Map? x1 /\ CBOR_Case_Map? x2 /\
    IT.mixed_list_length (CBOR_Case_Map?.v x1).cbor_map_ptr == len /\
    IT.mixed_list_length (CBOR_Case_Map?.v x2).cbor_map_ptr == len
  ))
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
: stt I16.t
    (cbor_raw_match_fuel n pm1 x1 v1 **
     cbor_raw_match_fuel n pm2 x2 v2 **
     pure (
       Map? (Ghost.reveal v1) /\ Map? (Ghost.reveal v2) /\
       List.Tot.length (map_v (Ghost.reveal v1)) == SZ.v len /\
       List.Tot.length (map_v (Ghost.reveal v2)) == SZ.v len
     ))
    (fun res ->
      cbor_raw_match_fuel n pm1 x1 v1 **
      cbor_raw_match_fuel n pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare_map_total (map_v (Ghost.reveal v1)) (map_v (Ghost.reveal v2)))))
