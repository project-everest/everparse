module CBOR.SteelST.Type.Def
open Steel.ST.OnRange
open Steel.ST.GenElim

module A = Steel.ST.Array
module U8 = FStar.UInt8
module GR = Steel.ST.GhostReference

let cbor_serialized_payload_t = A.array U8.t

let cbor_serialized_footprint_t = unit

let cbor_footprint_t = GR.ref unit

let dummy_cbor_footprint = GR.dummy_ref _
