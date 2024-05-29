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

[@@no_auto_projectors]
noeq
type cbor_read_t = {
  cbor_read_is_success: bool;
  cbor_read_payload: cbor;
  cbor_read_remainder: A.array U8.t;
  cbor_read_remainder_length: SZ.t;
}

noextract
let cbor_read_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: cbor_read_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= SZ.v c.cbor_read_remainder_length == Seq.length rem /\
  va `Seq.equal` (Cbor.serialize_cbor v `Seq.append` rem)

[@@__reduce__]
let cbor_read_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: cbor_read_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match full_perm c.cbor_read_payload v `star`
    A.pts_to c.cbor_read_remainder p rem `star`
    ((raw_data_item_match full_perm c.cbor_read_payload v `star` A.pts_to c.cbor_read_remainder p rem) `implies_`
      A.pts_to a p va) `star`
    pure (cbor_read_success_postcond va c v rem)
  ))

noextract
let cbor_read_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . ~ (Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff)

[@@__reduce__]
let cbor_read_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a p va `star` pure (cbor_read_error_postcond va)

let cbor_read_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: cbor_read_t)
: Tot vprop
= if res.cbor_read_is_success
  then cbor_read_success_post a p va res
  else cbor_read_error_post a p va

val cbor_read
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (a: A.array U8.t)
  (sz: SZ.t)
: ST cbor_read_t
    (A.pts_to a p va)
    (fun res -> cbor_read_post a p va res)
    (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    (fun _ -> True)

noextract
let cbor_read_deterministically_encoded_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: cbor_read_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= cbor_read_success_postcond va c v rem /\
  Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == true

[@@__reduce__]
let cbor_read_deterministically_encoded_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: cbor_read_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match full_perm c.cbor_read_payload v `star`
    A.pts_to c.cbor_read_remainder p rem `star`
    ((raw_data_item_match full_perm c.cbor_read_payload v `star` A.pts_to c.cbor_read_remainder p rem) `implies_`
      A.pts_to a p va) `star`
    pure (cbor_read_deterministically_encoded_success_postcond va c v rem)
  ))

noextract
let cbor_read_deterministically_encoded_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff ==> Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == false

[@@__reduce__]
let cbor_read_deterministically_encoded_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a p va `star` pure (cbor_read_deterministically_encoded_error_postcond va)

let cbor_read_deterministically_encoded_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: cbor_read_t)
: Tot vprop
= if res.cbor_read_is_success
  then cbor_read_deterministically_encoded_success_post a p va res
  else cbor_read_deterministically_encoded_error_post a p va

val cbor_read_deterministically_encoded
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (a: A.array U8.t)
  (sz: SZ.t)
: ST cbor_read_t
    (A.pts_to a p va)
    (fun res -> cbor_read_deterministically_encoded_post a p va res)
    (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    (fun _ -> True)
