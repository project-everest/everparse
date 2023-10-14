module CBOR.SteelST
open Steel.ST.Util

module Cbor = CBOR.Spec.Type
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array

noeq
type cbor_int = {
  typ: Cbor.major_type_uint64_or_neg_int64;
  value: U64.t;
}

noeq
type cbor_string = {
  typ: Cbor.major_type_byte_string_or_text_string;
  byte_length: U64.t;
  payload: A.array U8.t;
  permission: perm;
}

inline_for_extraction
noextract
val cbor_serialized_payload_t: Type0

[@@erasable]
val cbor_serialized_footprint_t: Type0

noeq
type cbor_serialized = {
  byte_size: SZ.t;
  payload: cbor_serialized_payload_t;
  footprint: cbor_serialized_footprint_t;
}

noeq
type cbor_tagged = {
  tag: U64.t;
  payload: R.ref cbor;
  footprint: Ghost.erased cbor;
}

and cbor_array = {
  count: U64.t;
  payload: A.array cbor;
  footprint: Ghost.erased (Seq.seq cbor);
}

and cbor_map_entry = {
  key: cbor;
  value: cbor;
}

and cbor_map = {
  entry_count: U64.t;
  payload: A.array cbor_map_entry;
  footprint: Ghost.erased (Seq.seq cbor_map_entry);
}

and cbor =
| CBOR_Case_Int64 of cbor_int
| CBOR_Case_String of cbor_string
| CBOR_Case_Tagged of cbor_tagged
| CBOR_Case_Array of cbor_array
| CBOR_Case_Map of cbor_map
| CBOR_Case_Simple_value of Cbor.simple_value
| CBOR_Case_Serialized of cbor_serialized

inline_for_extraction
noextract
let dummy_cbor : cbor = CBOR_Case_Simple_value 0uy

val raw_data_item_match
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop

val serialize_cbor
  (c: Cbor.raw_data_item)
: GTot (Seq.seq U8.t)

val serialize_cbor_inj
  (c1 c2: Cbor.raw_data_item)
: Lemma
  (requires (serialize_cbor c1 == serialize_cbor c2))
  (ensures (c1 == c2))

val serialize_cbor_nonempty
  (c: Cbor.raw_data_item)
: Lemma
  (Seq.length (serialize_cbor c) > 0)

noextract
let write_cbor_postcond
  (va: Cbor.raw_data_item)
  (out: A.array U8.t)
  (vout': Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
= let s = serialize_cbor va in
  Seq.length vout' == A.length out /\
  (res = 0sz <==> Seq.length s > Seq.length vout') /\
  (res <> 0sz ==> (
    SZ.v res == Seq.length s /\
    Seq.slice vout' 0 (Seq.length s) `Seq.equal` s
  ))

[@@__reduce__]
let write_cbor_post
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (res: SZ.t)
  (vout': Seq.seq U8.t)
: Tot vprop
= 
  A.pts_to out full_perm vout' `star`
  pure (write_cbor_postcond va out vout' res)

val write_cbor
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (#vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (sz: SZ.t)
: ST SZ.t
    (raw_data_item_match c (Ghost.reveal va) `star`
      A.pts_to out full_perm vout
    )
    (fun res -> 
      raw_data_item_match c (Ghost.reveal va) `star`
      exists_ (write_cbor_post va c vout out res)
    )
    (SZ.v sz == A.length out)
    (fun _ -> True)
