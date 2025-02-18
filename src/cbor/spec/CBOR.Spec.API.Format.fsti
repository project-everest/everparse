module CBOR.Spec.API.Format
include CBOR.Spec.API.Type

module U8 = FStar.UInt8
module U64 = FStar.UInt64

(** Parsing *)

val cbor_parse : (x: Seq.seq U8.t) -> Pure (option (cbor & nat))
  (requires True)
  (ensures (fun res -> match res with
  | None -> True
  | Some (_, n) -> n <= Seq.length x
  ))

val cbor_parse_prefix
  (x y: Seq.seq U8.t)
: Lemma
  (requires (match cbor_parse x with
  | Some (_, n) -> Seq.length y >= n /\ Seq.slice x 0 n == Seq.slice y 0 n
  | _ -> False
  ))
  (ensures (
    cbor_parse x == cbor_parse y
  ))

(** Deterministic parsing and serialization *)

val cbor_det_serialize: (x: cbor) -> Tot (Seq.seq U8.t)

val cbor_det_parse (x: Seq.seq U8.t) : Pure (option (cbor & nat))
  (requires True)
  (ensures (fun res -> match res with
  | None -> True
  | Some (y, n) -> 0 < n /\ n <= Seq.length x /\ cbor_parse x == res /\ cbor_det_serialize y == Seq.slice x 0 n // unique binary representation
  ))

let cbor_det_parse_inj
  (x1 x2: Seq.seq U8.t)
: Lemma
  (requires (match cbor_det_parse x1, cbor_det_parse x2 with
  | Some (y1, n1), Some (y2, n2) -> y1 == y2
  | _ -> False
  ))
  (ensures (match cbor_det_parse x1, cbor_det_parse x2 with
  | Some (y1, n1), Some (y2, n2) -> y1 == y2 /\ n1 == n2 /\ Seq.slice x1 0 n1 == Seq.slice x2 0 n2
  | _ -> False
  ))
= let Some (y1, n1) = cbor_det_parse x1 in
  let Some (y2, n2) = cbor_det_parse x2 in
  assert (Seq.slice x1 0 n1 == Seq.slice x2 0 n2);
  assert (Seq.length (Seq.slice x1 0 n1) == Seq.length (Seq.slice x2 0 n2))

val cbor_det_parse_prefix
  (x y: Seq.seq U8.t)
: Lemma
  (requires (match cbor_det_parse x with
  | Some (_, n) -> Seq.length y >= n /\ Seq.slice x 0 n `Seq.equal` Seq.slice y 0 n
  | _ -> False
  ))
  (ensures (
    cbor_det_parse x == cbor_det_parse y
  ))

val cbor_det_serialize_parse (x: cbor) : Lemma
  (let s = cbor_det_serialize x in
    cbor_det_parse s == Some (x, Seq.length s)
  )

let cbor_det_serialize_parse'
  (x: cbor)
  (y: Seq.seq U8.t)
: Lemma
  (let s = cbor_det_serialize x in
    cbor_det_parse (s `Seq.append` y) == Some (x, Seq.length s)
  )
= let s = cbor_det_serialize x in
  cbor_det_serialize_parse x;
  cbor_det_parse_prefix s (s `Seq.append` y)

let cbor_det_parse_none_equiv
  (v: Seq.seq U8.t)
: Lemma
  (None? (cbor_det_parse v) <==> ~ (exists v1 v2 . v == cbor_det_serialize v1 `Seq.append` v2))
= Classical.forall_intro_2 cbor_det_serialize_parse';
  match cbor_det_parse v with
  | None -> ()
  | Some (_, consumed) -> Seq.lemma_split v consumed

let cbor_det_serialize_inj_strong
  (x1 x2: cbor)
  (y1 y2: Seq.seq U8.t)
: Lemma
  (requires (cbor_det_serialize x1 `Seq.append` y1 == cbor_det_serialize x2 `Seq.append` y2))
  (ensures (x1 == x2 /\ y1 == y2))
= cbor_det_serialize_parse' x1 y1;
  cbor_det_serialize_parse' x2 y2;
  Seq.lemma_append_inj
    (cbor_det_serialize x1)
    y1
    (cbor_det_serialize x2)
    y2

let cbor_det_serialize_inj_strong'
  (x1: cbor)
  (y1: Seq.seq U8.t)
  (x2: cbor)
  (y2: Seq.seq U8.t)
: Lemma
  (cbor_det_serialize x1 `Seq.append` y1 == cbor_det_serialize x2 `Seq.append` y2 ==> (x1 == x2 /\ y1 == y2))
= Classical.move_requires (cbor_det_serialize_inj_strong x1 x2 y1) y2

let cbor_det_serialize_inj
  (x1 x2: cbor)
: Lemma
  (requires (cbor_det_serialize x1 == cbor_det_serialize x2))
  (ensures (x1 == x2))
= Seq.append_empty_r (cbor_det_serialize x1);
  Seq.append_empty_r (cbor_det_serialize x2);
  cbor_det_serialize_inj_strong x1 x2 Seq.empty Seq.empty

val cbor_det_serialize_tag
  (tag: U64.t)
: Tot (Seq.seq U8.t)

val cbor_det_serialize_tag_length
  (tag: U64.t)
: Lemma
  (Seq.length (cbor_det_serialize_tag tag) > 0)

val cbor_det_serialize_tag_correct
  (tag: U64.t)
  (payload: cbor)
: Lemma
  (cbor_det_serialize (pack (CTagged tag payload)) == cbor_det_serialize_tag tag `Seq.append` cbor_det_serialize payload)
