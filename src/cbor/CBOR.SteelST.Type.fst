module CBOR.SteelST.Type
open Steel.ST.OnRange
open Steel.ST.GenElim
open CBOR.SteelST.Type.Def

module CborST = CBOR.SteelST.Raw
module LPA = LowParse.SteelST.ArrayPtr.IntroElim
module LPS = LowParse.SteelST.SeqMatch
module LW = LowParse.SteelST.L2ROutput.IntroElim
module GR = Steel.ST.GhostReference

let cbor_map_entry = cbor_map_entry

let cbor = cbor

let dummy_cbor : cbor = CBOR_Case_Simple_value 0uy dummy_cbor_footprint

let cbor_map_entry_key = Mkcbor_map_entry?.cbor_map_entry_key
let cbor_map_entry_value = Mkcbor_map_entry?.cbor_map_entry_value

let cbor_map_entry_key_value_inj
  m1 m2
= ()

let mk_cbor_map_entry
  k v
= Mkcbor_map_entry k v
