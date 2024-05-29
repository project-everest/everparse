module CBOR.SteelST.Type
open Steel.ST.OnRange
open Steel.ST.GenElim
open CBOR.SteelST.Type.Def

module GR = Steel.ST.GhostReference

let cbor_map_entry = cbor_map_entry

let cbor = cbor

let cbor_array_iterator_t = cbor_array_iterator_t

let cbor_map_iterator_t = cbor_map_iterator_t
