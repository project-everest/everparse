module CBOR.SteelST.Type
open Steel.ST.OnRange
open Steel.ST.GenElim
open CBOR.SteelST.Type.Def

module GR = Steel.ST.GhostReference

let cbor_map_entry = cbor_map_entry

let cbor = cbor

let dummy_cbor : cbor = CBOR_Case_Simple_value 0uy dummy_cbor_footprint

let cbor_map_entry_key x = match x with
| Mkcbor_map_entry k _ -> k

let cbor_map_entry_value x = match x with
| Mkcbor_map_entry _ v -> v

let cbor_map_entry_key_value_inj
  m1 m2
= ()

let mk_cbor_map_entry
  k v
= Mkcbor_map_entry k v

let cbor_array_iterator_t = cbor_array_iterator_t

let cbor_map_iterator_t = cbor_map_iterator_t
