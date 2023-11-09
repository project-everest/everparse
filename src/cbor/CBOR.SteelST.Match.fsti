module CBOR.SteelST.Match
include CBOR.SteelST.Type
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

(* Relating a CBOR C object with a CBOR high-level value *)

noextract
let fstp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a1 = fst x

noextract
let sndp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a2 = snd x

[@@__reduce__]
let raw_data_item_map_entry_match1
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v1 }) -> vprop))
: Tot vprop
= raw_data_item_match (cbor_map_entry_key c1) (fstp v1) `star`
  raw_data_item_match (cbor_map_entry_value c1) (sndp v1)

val raw_data_item_match
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop

let raw_data_item_array_match
  (p: perm)
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= SM.seq_list_match c v (raw_data_item_match p)

[@@__reduce__]
let raw_data_item_map_entry_match
  (p: perm)
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
= raw_data_item_map_entry_match1 c1 v1 (raw_data_item_match p)

let raw_data_item_map_match
  (p: perm)
  (c: Seq.seq cbor_map_entry)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
  (decreases v)
= SM.seq_list_match c v (raw_data_item_map_entry_match p)

(* `cbor_is_equal_aux` is an auxiliary function intended to compare two CBOR objects
   represented by their serialized bytes. It returns an inconclusive result if one of
   the two is not such an object. The full equality test is implemented in Pulse, see
   `CBOR.Pulse.cbor_is_equal`
*)

noeq [@@no_auto_projectors]
type cbor_is_equal_aux_t
= | CborEqual
  | CborNotEqual
  | CborCompareFailure

noextract
let cbor_is_equal_aux_postcond
  (v1 v2: Cbor.raw_data_item)
  (res: cbor_is_equal_aux_t)
: Tot prop
= match res with
  | CborEqual -> v1 == v2
  | CborNotEqual -> ~ (v1 == v2)
  | _ -> True

val cbor_is_equal_aux
  (#p1 #p2: perm)
  (#v1 #v2: Ghost.erased Cbor.raw_data_item)
  (c1 c2: cbor)
: STT cbor_is_equal_aux_t
    (raw_data_item_match p1 c1 v1 `star` raw_data_item_match p2 c2 v2)
    (fun res -> raw_data_item_match p1 c1 v1 `star` raw_data_item_match p2 c2 v2 `star`
      pure (cbor_is_equal_aux_postcond v1 v2 res)
    )
