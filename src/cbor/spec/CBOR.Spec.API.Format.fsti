module CBOR.Spec.API.Format
include CBOR.Spec.API.Type

module U8 = FStar.UInt8
module U64 = FStar.UInt64

(** Parsing *)

val cbor_parse : (x: Seq.seq U8.t) -> Pure (option (cbor & nat))
  (requires True)
  (ensures (fun res -> match res with
  | None -> True
  | Some (_, n) -> 0 < n /\ n <= Seq.length x
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

val cbor_det_serialize_list
  (l: list cbor)
: Tot (Seq.seq U8.t)

val cbor_det_serialize_list_nil (_: unit) : Lemma
  (cbor_det_serialize_list [] == Seq.empty)

val cbor_det_serialize_list_cons (a: cbor) (q: list cbor) : Lemma
  (cbor_det_serialize_list (a :: q) == cbor_det_serialize a `Seq.append` cbor_det_serialize_list q)

let rec cbor_det_serialize_list_append (l1 l2: list cbor) : Lemma
  (ensures (cbor_det_serialize_list (l1 `List.Tot.append` l2) `Seq.equal` (cbor_det_serialize_list l1 `Seq.append` cbor_det_serialize_list l2)))
  (decreases l1)
= match l1 with
  | [] -> cbor_det_serialize_list_nil ()
  | b :: q ->
    List.Tot.append_assoc [b] q l2;
    cbor_det_serialize_list_append q l2;
    cbor_det_serialize_list_cons b (List.Tot.append q l2);
    cbor_det_serialize_list_cons b q

let cbor_det_serialize_list_snoc (h: list cbor) (a: cbor) : Lemma
  (ensures (cbor_det_serialize_list (h `List.Tot.append` [a]) `Seq.equal` (cbor_det_serialize_list h `Seq.append` cbor_det_serialize a)))
= cbor_det_serialize_list_nil ();
  cbor_det_serialize_list_cons a [];
  cbor_det_serialize_list_append h [a]

val cbor_det_serialize_array_length_gt_list
  (l: list cbor)
: Lemma
  (requires (FStar.UInt.fits (List.Tot.length l) 64))
  (ensures (
    FStar.UInt.fits (List.Tot.length l) 64 /\
    Seq.length (cbor_det_serialize (pack (CArray l))) > Seq.length (cbor_det_serialize_list l)
  ))

val cbor_det_serialize_string_length_gt
  (ty: major_type_byte_string_or_text_string)
  (l: Seq.seq U8.t)
: Lemma
  (requires (FStar.UInt.fits (Seq.length l) 64 /\
    (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct l)
  ))
  (ensures (
    FStar.UInt.fits (Seq.length l) 64 /\
    (ty == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct l) /\
    Seq.length (cbor_det_serialize (pack (CString ty l))) > Seq.length l
  ))

val cbor_det_serialize_map
  (m: cbor_map)
: Tot (Seq.seq U8.t)

val cbor_det_serialize_map_empty (_: unit) : Lemma
  (cbor_det_serialize_map cbor_map_empty == Seq.empty)

val cbor_det_serialize_map_singleton
  (key: cbor)
  (value: cbor)
: Lemma
  (cbor_det_serialize_map (cbor_map_singleton key value) == cbor_det_serialize key `Seq.append` cbor_det_serialize value)

val cbor_det_serialize_map_append_length
  (m1 m2: cbor_map)
: Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures (Seq.length (cbor_det_serialize_map (cbor_map_union m1 m2)) == Seq.length (cbor_det_serialize_map m1) + Seq.length (cbor_det_serialize_map m2)))

val cbor_det_serialize_map_length_gt_list
  (l: cbor_map)
: Lemma
  (requires (FStar.UInt.fits (cbor_map_length l) 64))
  (ensures (
    FStar.UInt.fits (cbor_map_length l) 64 /\
    Seq.length (cbor_det_serialize (pack (CMap l))) > Seq.length (cbor_det_serialize_map l)
  ))

val cbor_det_parse_map
  (n: nat)
  (s: Seq.seq U8.t)
: Pure (option (cbor_map & nat))
  (requires True)
  (ensures fun res -> match res with
  | None -> True
  | Some (_, len) ->
    len <= Seq.length s
  )

val cbor_det_parse_map_prefix
  (n: nat)
  (s1 s2: Seq.seq U8.t)
: Lemma
  (match cbor_det_parse_map n s1 with
  | None -> True
  | Some (l, len1) ->
    (len1 <= Seq.length s2 /\ Seq.slice s1 0 len1 == Seq.slice s2 0 len1) ==>
    cbor_det_parse_map n s2 == Some (l, len1)
  )

val cbor_det_parse_map_equiv
  (n: nat)
  (s: Seq.seq U8.t)
  (l: cbor_map)
  (len: nat)
: Lemma
  (cbor_det_parse_map n s == Some (l, len) <==> (
    n == cbor_map_length l /\
    len <= Seq.length s /\
    Seq.slice s 0 len == cbor_det_serialize_map l
  ))
