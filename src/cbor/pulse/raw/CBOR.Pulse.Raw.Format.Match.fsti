module CBOR.Pulse.Raw.Format.Match
include CBOR.Pulse.Raw.Type
open CBOR.Spec.Raw.Base
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module SZ = FStar.SizeT

val cbor_match_serialized_payload_array
  (c: slice U8.t)
  (p: perm)
  (r: list raw_data_item)
: Tot slprop

val cbor_match_serialized_payload_map
  (c: slice U8.t)
  (p: perm)
  (r: list (raw_data_item & raw_data_item))
: Tot slprop

val cbor_match_serialized_payload_tagged
  (c: slice U8.t)
  (p: perm)
  (r: raw_data_item)
: Tot slprop
