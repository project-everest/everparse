module CBOR.SteelST.Type.Def
open Steel.ST.OnRange
open Steel.ST.GenElim

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let cbor_serialized_payload_t = LPS.byte_array

let cbor_serialized_footprint_t = LPA.array LPS.byte

let cbor_footprint_t = GR.ref unit

let dummy_cbor_footprint = GR.dummy_ref _
