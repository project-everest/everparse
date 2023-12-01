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

val dummy_cbor : cbor

val cbor_map_entry_key: cbor_map_entry -> cbor

val cbor_map_entry_value: cbor_map_entry -> cbor

val cbor_map_entry_key_value_inj
  (m1 m2: cbor_map_entry)
: Lemma
  (requires (
    cbor_map_entry_key m1 == cbor_map_entry_key m2 /\
    cbor_map_entry_value m1 == cbor_map_entry_value m2
  ))
  (ensures (m1 == m2))
  [SMTPatOr [
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_value m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_value m2)];
  ]]

val mk_cbor_map_entry
  (key: cbor)
  (value: cbor)
: Pure cbor_map_entry
  (requires True)
  (ensures (fun res ->
    cbor_map_entry_key res == key /\
    cbor_map_entry_value res == value
  ))

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

(* `cbor_compare_aux` is an auxiliary function intended to compare two CBOR objects
   represented by their serialized bytes. It returns an inconclusive result if one of
   the two is not such an object. The full comparison test is implemented in Pulse, see
   `CBOR.Pulse.cbor_compare`
*)

noextract
let cbor_compare_aux_postcond
  (v1 v2: Cbor.raw_data_item)
  (res: FStar.Int16.t)
: Tot prop
= let nres = FStar.Int16.v res in
  (nres = -1 || nres = 0 || nres = 1) ==> nres == Cbor.cbor_compare v1 v2

val cbor_compare_aux
  (#p1 #p2: perm)
  (#v1 #v2: Ghost.erased Cbor.raw_data_item)
  (c1 c2: cbor)
: STT FStar.Int16.t
    (raw_data_item_match p1 c1 v1 `star` raw_data_item_match p2 c2 v2)
    (fun res -> raw_data_item_match p1 c1 v1 `star` raw_data_item_match p2 c2 v2 `star`
      pure (cbor_compare_aux_postcond v1 v2 res)
    )
