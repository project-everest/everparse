module CBOR.Pulse.Raw.EverParse.Det.Compare.Dispatch.String
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.Compare.Base
open CBOR.Pulse.Raw.Compare.Bytes
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module I16 = FStar.Int16
module Trade = Pulse.Lib.Trade.Util

inline_for_extraction
val cbor_compare_dispatch_string_case
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: stt I16.t
    (cbor_raw_match_fuel n pm1 x1 v1 **
     cbor_raw_match_fuel n pm2 x2 v2 **
     pure (String? (Ghost.reveal v1) /\ String? (Ghost.reveal v2) /\
           String?.typ (Ghost.reveal v1) == String?.typ (Ghost.reveal v2)))
    (fun res ->
      cbor_raw_match_fuel n pm1 x1 v1 **
      cbor_raw_match_fuel n pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare v1 v2)))
