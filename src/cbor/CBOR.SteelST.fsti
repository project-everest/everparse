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
  cbor_int_type: Cbor.major_type_uint64_or_neg_int64;
  cbor_int_value: U64.t;
}

noeq
type cbor_string = {
  cbor_string_type: Cbor.major_type_byte_string_or_text_string;
  cbor_string_length: U64.t;
  cbor_string_payload: A.array U8.t;
  permission: perm; // ghost
}

inline_for_extraction
noextract
val cbor_serialized_payload_t: Type0 // extracted as uint8_t*

[@@erasable]
val cbor_serialized_footprint_t: Type0

noeq
type cbor_serialized = {
  cbor_serialized_size: SZ.t;
  cbor_serialized_payload: cbor_serialized_payload_t;
  footprint: cbor_serialized_footprint_t; // ghost
}

noeq
type cbor_tagged = {
  cbor_tagged_tag: U64.t;
  cbor_tagged_payload: R.ref cbor;
  footprint: Ghost.erased cbor; // ghost
}

and cbor_array = {
  cbor_array_length: U64.t;
  cbor_array_payload: A.array cbor;
  footprint: Ghost.erased (Seq.seq cbor); // ghost
}

and cbor_map_entry = {
  cbor_map_entry_key: cbor;
  cbor_map_entry_value: cbor;
}

and cbor_map = {
  cbor_map_length: U64.t;
  cbor_map_payload: A.array cbor_map_entry;
  footprint: Ghost.erased (Seq.seq cbor_map_entry); // ghost
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
  (s1 s2: Seq.seq U8.t)
: Lemma
  (requires (serialize_cbor c1 `Seq.append` s1 == serialize_cbor c2 `Seq.append` s2))
  (ensures (c1 == c2 /\ s1 == s2))

val serialize_cbor_nonempty
  (c: Cbor.raw_data_item)
: Lemma
  (Seq.length (serialize_cbor c) > 0)

noeq
type read_cbor_success_t = {
  read_cbor_payload: cbor;
  read_cbor_remainder: A.array U8.t;
  read_cbor_remainder_length: SZ.t;
}

noeq
type read_cbor_t =
| ParseError
| ParseSuccess of read_cbor_success_t

noextract
let read_cbor_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= SZ.v c.read_cbor_remainder_length == Seq.length rem /\
  va `Seq.equal` (serialize_cbor v `Seq.append` rem)

[@@__reduce__]
let read_cbor_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match c.read_cbor_payload v `star`
    A.pts_to c.read_cbor_remainder p rem `star`
    ((raw_data_item_match c.read_cbor_payload v `star` A.pts_to c.read_cbor_remainder p rem) `implies_`
      A.pts_to a p va) `star`
    pure (read_cbor_success_postcond va c v rem)
  ))

noextract
let read_cbor_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v . ~ (serialize_cbor v == Seq.slice va 0 (min (Seq.length (serialize_cbor v)) (Seq.length va)))

[@@__reduce__]
let read_cbor_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a p va `star` pure (read_cbor_error_postcond va)

let read_cbor_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: read_cbor_t)
: Tot vprop
= match res with
  | ParseError -> read_cbor_error_post a p va
  | ParseSuccess c -> read_cbor_success_post a p va c

val read_cbor
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (a: A.array U8.t)
  (sz: SZ.t)
: ST read_cbor_t
    (A.pts_to a p va)
    (fun res -> read_cbor_post a p va res)
    (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    (fun _ -> True)

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
