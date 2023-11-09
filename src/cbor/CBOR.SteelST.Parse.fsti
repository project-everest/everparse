module CBOR.SteelST.Parse
include CBOR.SteelST.Match
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

(* Parsing *)

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
  va `Seq.equal` (Cbor.serialize_cbor v `Seq.append` rem)

[@@__reduce__]
let read_cbor_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match full_perm c.read_cbor_payload v `star`
    A.pts_to c.read_cbor_remainder p rem `star`
    ((raw_data_item_match full_perm c.read_cbor_payload v `star` A.pts_to c.read_cbor_remainder p rem) `implies_`
      A.pts_to a p va) `star`
    pure (read_cbor_success_postcond va c v rem)
  ))

noextract
let read_cbor_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . ~ (Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff)

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
let read_deterministically_encoded_cbor_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= read_cbor_success_postcond va c v rem /\
  Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == true

[@@__reduce__]
let read_deterministically_encoded_cbor_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match full_perm c.read_cbor_payload v `star`
    A.pts_to c.read_cbor_remainder p rem `star`
    ((raw_data_item_match full_perm c.read_cbor_payload v `star` A.pts_to c.read_cbor_remainder p rem) `implies_`
      A.pts_to a p va) `star`
    pure (read_deterministically_encoded_cbor_success_postcond va c v rem)
  ))

noextract
let read_deterministically_encoded_cbor_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff ==> Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == false

[@@__reduce__]
let read_deterministically_encoded_cbor_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a p va `star` pure (read_deterministically_encoded_cbor_error_postcond va)

let read_deterministically_encoded_cbor_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: read_cbor_t)
: Tot vprop
= match res with
  | ParseError -> read_deterministically_encoded_cbor_error_post a p va
  | ParseSuccess c -> read_deterministically_encoded_cbor_success_post a p va c

val read_deterministically_encoded_cbor
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (a: A.array U8.t)
  (sz: SZ.t)
: ST read_cbor_t
    (A.pts_to a p va)
    (fun res -> read_deterministically_encoded_cbor_post a p va res)
    (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    (fun _ -> True)
