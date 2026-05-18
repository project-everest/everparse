module CBOR.Pulse.Raw.EverParse.Match.Fuel
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Match

open CBOR.Spec.Raw.EverParse
open CBOR.Spec.Raw.Base
open LowParse.Pulse.Base
open LowParse.Pulse.VCList
open LowParse.Pulse.Combinators
open LowParse.PulseParse.Projectors
open LowParse.PulseParse.Base
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type

let rec cbor_raw_match_fuel
  (n: nat)
:
  (pm: perm) ->
  (xl: cbor_raw) ->
  (xh: raw_data_item) ->
  Tot slprop
= if n = 0
  then fun _ _ _ -> pure False
  else cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1))
