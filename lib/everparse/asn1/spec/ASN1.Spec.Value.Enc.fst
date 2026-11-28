module ASN1.Spec.Value.Enc

(* The DER encoding of generic ASN.1 values, as a Tot function, and the
   proof that the bytes consumed by the ANY parser are exactly the encoding
   of the value it returns *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.SeqBytes
open LowParse.Tot.List

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.IdentifierU32.Enc
open ASN1.Spec.LengthU32
open ASN1.Spec.Value

module RV = LowParse.Spec.RecursiveVLGen
module LPDER = LowParse.Spec.DER
module LPB = LowParse.Spec.BoundedInt
module E = FStar.Endianness
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module Seq = FStar.Seq

(* Lengths (X.690 8.1.3, 10.1) *)

let enc_len (y: U32.t) : Tot bytes =
  let x = LPDER.tag_of_der_length32_impl y in
  let s1 = Seq.create 1 x in
  if x `U8.lt` 128uy
  then s1
  else if x = 129uy
  then s1 `Seq.append` Seq.create 1 (Cast.uint32_to_uint8 y)
  else s1 `Seq.append` E.n_to_be (LPB.log256' (U32.v y)) (U32.v y)

let enc_len_eq (y: U32.t)
: Lemma
  (enc_len y == serialize serialize_asn1_length_u32_t y)
= LPDER.serialize_bounded_der_length32_unfold 0 4294967295 y;
  let x = LPDER.tag_of_der_length32_impl y in
  if x `U8.lt` 128uy || x = 129uy
  then Seq.lemma_eq_elim (enc_len y) (serialize serialize_asn1_length_u32_t y)
  else begin
    LPB.serialize_bounded_integer_spec (LPB.log256' (U32.v y)) y;
    Seq.lemma_eq_elim (enc_len y) (serialize serialize_asn1_length_u32_t y)
  end

let parse_enc_len (y: U32.t) (suffix: bytes)
: Lemma
  (parse parse_asn1_length_u32_t (enc_len y `Seq.append` suffix) == Some (y, Seq.length (enc_len y)))
= enc_len_eq y;
  parse_strong_prefix #parse_asn1_length_u32_t_kind parse_asn1_length_u32_t (enc_len y) (enc_len y `Seq.append` suffix)

let parse_len_consumed (b: bytes)
: Lemma
  (match parse parse_asn1_length_u32_t b with
   | Some (y, c) -> Seq.slice b 0 c == enc_len y
   | None -> True)
= match parse parse_asn1_length_u32_t b with
  | Some (y, c) ->
    let e = enc_len y in
    parse_enc_len y Seq.empty;
    Seq.append_empty_r e;
    parse_injective #parse_asn1_length_u32_t_kind parse_asn1_length_u32_t b e;
    Seq.lemma_eq_elim (Seq.slice e 0 (Seq.length e)) e
  | None -> ()

(* Headers. If the constructor of a value agrees with the
   primitive/constructed flag of its identifier (`ok`) and its contents are
   shorter than 2^32 bytes, then its header is the DER length of its contents.
   Otherwise, the header starts with 0xFF, which no DER length starts with
   (X.690 8.1.3.5 c), so that the ANY parser never accepts it. This makes the
   encoding injective on all values (`asn1_value_enc_inj` below.) *)

let enc_unary (n: nat) : Tot bytes =
  Seq.create n 1uy `Seq.append` Seq.create 1 0uy

let enc_hdr (ok: bool) (n: nat) : Tot bytes =
  if ok && n < 4294967296
  then enc_len (U32.uint_to_t n)
  else Seq.create 1 0xFFuy `Seq.append` (Seq.create 1 (if ok then 0uy else 1uy) `Seq.append` enc_unary n)

let enc_tlv (id: asn1_id_t) (ok: bool) (c: bytes) : Tot bytes =
  asn1_id_enc id `Seq.append` (enc_hdr ok (Seq.length c) `Seq.append` c)

(* Values *)

let rec asn1_value_enc (v: asn1_value) : Tot bytes (decreases v) =
  match v with
  | ASN1_VALUE_PRIMITIVE id b ->
    enc_tlv id (PRIMITIVE? id.f) b
  | ASN1_VALUE_CONSTRUCTED id l ->
    enc_tlv id (CONSTRUCTED? id.f) (asn1_value_list_enc l)

and asn1_value_list_enc (l: list asn1_value) : Tot bytes (decreases l) =
  match l with
  | [] -> Seq.empty
  | v :: q -> asn1_value_enc v `Seq.append` asn1_value_list_enc q

let parse_any_identifier_consumed (b: bytes)
: Lemma
  (match parse parse_asn1_any_identifier b with
   | Some (id, c) -> Seq.slice b 0 c == asn1_id_enc id /\ parse parse_asn1_identifier_U32 b == Some ((id <: asn1_id_t), c)
   | None -> (match parse parse_asn1_identifier_U32 b with Some (id, _) -> asn1_any_id_valid id == false | None -> True))
= lemma_parse_asn1_identifier_first_inj ();
  parse_filter_eq (parse_u8 `and_then` parse_asn1_identifier_first) asn1_any_id_valid b;
  parse_asn1_identifier_U32_consumed b

let pv = RV.parse_rec_vlgen asn1_value_param

let parse_asn1_any_leaf_eq (id: asn1_any_id_t) (b: bytes)
: Lemma
  (parse (parse_asn1_any_leaf id) b == (if asn1_any_leaf_ok id b then Some (b, Seq.length b) else None))
= parse_synth_eq (parse_seq_all_bytes `parse_filter` asn1_any_leaf_ok id) (synth_asn1_any_leaf id) b;
  parse_filter_eq parse_seq_all_bytes (asn1_any_leaf_ok id) b;
  parse_seq_all_bytes_correct ()

(* The contents of a value, after its header *)
let rec_vlgen_body_eq (id: asn1_any_id_t) (b: bytes)
: Lemma
  (parse (RV.rec_vlgen_body asn1_value_param pv id) b == (
    if CONSTRUCTED? id.f
    then match parse (tot_parse_list pv) b with
      | Some (l, c) -> Some (RV.RNode l, c)
      | None -> None
    else if asn1_any_leaf_ok id b then Some (RV.RLeaf b, Seq.length b) else None))
= if CONSTRUCTED? id.f
  then tot_parse_synth_eq (tot_parse_list pv) (RV.RNode #asn1_value #asn1_octetstring_t) b
  else begin
    tot_parse_synth_eq (parse_asn1_any_leaf id) (RV.RLeaf #asn1_value #asn1_octetstring_t) b;
    parse_asn1_any_leaf_eq id b
  end

let slice_3 (b: bytes) (c1 c2 len: nat)
: Lemma
  (requires (c1 + c2 + len <= Seq.length b))
  (ensures (Seq.slice b 0 (c1 + c2 + len) == Seq.slice b 0 c1 `Seq.append` (Seq.slice (Seq.slice b c1 (Seq.length b)) 0 c2 `Seq.append` Seq.slice b (c1 + c2) (c1 + c2 + len))))
= Seq.lemma_eq_elim (Seq.slice b 0 (c1 + c2 + len)) (Seq.slice b 0 c1 `Seq.append` (Seq.slice (Seq.slice b c1 (Seq.length b)) 0 c2 `Seq.append` Seq.slice b (c1 + c2) (c1 + c2 + len)))

let slice_2 (b: bytes) (n: nat)
: Lemma
  (requires (n <= Seq.length b))
  (ensures (b == Seq.slice b 0 n `Seq.append` Seq.slice b n (Seq.length b)))
= Seq.lemma_eq_elim b (Seq.slice b 0 n `Seq.append` Seq.slice b n (Seq.length b))

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let rec parse_asn1_value_consumed (b: bytes)
: Lemma
  (ensures (match parse pv b with
   | Some (v, n) -> Seq.slice b 0 n == asn1_value_enc v
   | None -> True))
  (decreases %[Seq.length b; 0])
= RV.parse_rec_vlgen_eq asn1_value_param b;
  match parse pv b with
  | None -> ()
  | Some (v, n) ->
    parse_any_identifier_consumed b;
    let Some (id, c1) = parse parse_asn1_any_identifier b in
    let b1 = Seq.slice b c1 (Seq.length b) in
    parse_len_consumed b1;
    let Some (len, c2) = parse parse_asn1_length_u32_t b1 in
    let hs = c1 + c2 in
    parser_kind_prop_equiv asn1_any_identifier_kind parse_asn1_any_identifier;
    assert (c1 > 0);
    assert (RV.rec_vlgen_header asn1_value_param b == Some (id, hs, U32.v len));
    assert (hs + U32.v len <= Seq.length b /\ n == hs + U32.v len);
    let ct = Seq.slice b hs (hs + U32.v len) in
    rec_vlgen_body_eq id ct;
    assert (U32.uint_to_t (U32.v len) == len);
    if CONSTRUCTED? id.f
    then begin
      parse_asn1_value_list_consumed ct;
      let Some (l, _) = parse (tot_parse_list pv) ct in
      assert (v == ASN1_VALUE_CONSTRUCTED id l)
    end else begin
      assert (v == ASN1_VALUE_PRIMITIVE id ct)
    end;
    assert (enc_hdr true (U32.v len) == enc_len len);
    slice_3 b c1 c2 (U32.v len)

and parse_asn1_value_list_consumed (b: bytes)
: Lemma
  (ensures (match parse (tot_parse_list pv) b with
   | Some (l, n) -> n == Seq.length b /\ b == asn1_value_list_enc l
   | None -> True))
  (decreases %[Seq.length b; 1])
= tot_parse_list_eq pv b;
  if Seq.length b = 0
  then Seq.lemma_eq_elim b Seq.empty
  else match parse pv b with
  | None -> ()
  | Some (v, n) ->
    if n = 0 then ()
    else begin
      parse_asn1_value_consumed b;
      let b' = Seq.slice b n (Seq.length b) in
      parse_asn1_value_list_consumed b';
      parser_kind_prop_equiv (parse_list_kind true) (tot_parse_list pv);
      slice_2 b n
    end
#pop-options

let parse_asn1_value_consumed' (b: bytes)
: Lemma
  (match parse parse_asn1_value b with
   | Some (v, n) -> Seq.slice b 0 n == asn1_value_enc v
   | None -> True)
= parse_asn1_value_consumed b

(* Injectivity of the encoding *)

let append_inj (a1 s1 a2 s2: bytes)
: Lemma
  (requires (Seq.length a1 == Seq.length a2 /\ a1 `Seq.append` s1 == a2 `Seq.append` s2))
  (ensures (a1 == a2 /\ s1 == s2))
= Seq.lemma_append_inj a1 s1 a2 s2;
  Seq.lemma_eq_elim a1 a2;
  Seq.lemma_eq_elim s1 s2

let append_assoc_3 (a b c: bytes)
: Lemma ((a `Seq.append` b) `Seq.append` c == a `Seq.append` (b `Seq.append` c))
= Seq.append_assoc a b c

let index_append_l (a s: bytes) (i: nat)
: Lemma
  (requires (i < Seq.length a))
  (ensures (i < Seq.length (a `Seq.append` s) /\ Seq.index (a `Seq.append` s) i == Seq.index a i))
= ()

let enc_unary_index (n: nat) (s: bytes) (i: nat)
: Lemma
  (requires (i <= n))
  (ensures (i < Seq.length (enc_unary n `Seq.append` s) /\
    Seq.index (enc_unary n `Seq.append` s) i == (if i = n then 0uy else 1uy)))
= index_append_l (enc_unary n) s i

let enc_unary_prefix_free (n1 n2: nat) (s1 s2: bytes)
: Lemma
  (requires (enc_unary n1 `Seq.append` s1 == enc_unary n2 `Seq.append` s2))
  (ensures (n1 == n2 /\ s1 == s2))
= if n1 < n2
  then begin enc_unary_index n1 s1 n1; enc_unary_index n2 s2 n1 end
  else if n2 < n1
  then begin enc_unary_index n1 s1 n2; enc_unary_index n2 s2 n2 end
  else append_inj (enc_unary n1) s1 (enc_unary n2) s2

let enc_len_head (y: U32.t)
: Lemma (Seq.length (enc_len y) > 0 /\ U8.v (Seq.index (enc_len y) 0) <= 132)
= let _ = LPDER.tag_of_der_length32' (U32.v y) in
  let x = LPDER.tag_of_der_length32_impl y in
  let s1 = Seq.create 1 x in
  if x `U8.lt` 128uy
  then ()
  else if x = 129uy
  then index_append_l s1 (Seq.create 1 (Cast.uint32_to_uint8 y)) 0
  else index_append_l s1 (E.n_to_be (LPB.log256' (U32.v y)) (U32.v y)) 0

let enc_len_prefix_free (y1 y2: U32.t) (s1 s2: bytes)
: Lemma
  (requires (enc_len y1 `Seq.append` s1 == enc_len y2 `Seq.append` s2))
  (ensures (y1 == y2 /\ s1 == s2))
= parse_enc_len y1 s1;
  parse_enc_len y2 s2;
  append_inj (enc_len y1) s1 (enc_len y2) s2

let enc_hdr_prefix_free (ok1 ok2: bool) (n1 n2: nat) (s1 s2: bytes)
: Lemma
  (requires (enc_hdr ok1 n1 `Seq.append` s1 == enc_hdr ok2 n2 `Seq.append` s2))
  (ensures (ok1 == ok2 /\ n1 == n2 /\ s1 == s2))
= let small1 = ok1 && n1 < 4294967296 in
  let small2 = ok2 && n2 < 4294967296 in
  let ff = Seq.create 1 0xFFuy in
  let d (ok: bool) = Seq.create 1 (if ok then 0uy else 1uy) in
  if small1 && small2
  then enc_len_prefix_free (U32.uint_to_t n1) (U32.uint_to_t n2) s1 s2
  else if small1
  then begin
    enc_len_head (U32.uint_to_t n1);
    index_append_l (enc_len (U32.uint_to_t n1)) s1 0;
    index_append_l ff ((d ok2 `Seq.append` enc_unary n2) `Seq.append` s2) 0;
    append_assoc_3 ff (d ok2 `Seq.append` enc_unary n2) s2
  end
  else if small2
  then begin
    enc_len_head (U32.uint_to_t n2);
    index_append_l (enc_len (U32.uint_to_t n2)) s2 0;
    index_append_l ff ((d ok1 `Seq.append` enc_unary n1) `Seq.append` s1) 0;
    append_assoc_3 ff (d ok1 `Seq.append` enc_unary n1) s1
  end
  else begin
    append_assoc_3 ff (d ok1 `Seq.append` enc_unary n1) s1;
    append_assoc_3 ff (d ok2 `Seq.append` enc_unary n2) s2;
    append_inj ff ((d ok1 `Seq.append` enc_unary n1) `Seq.append` s1) ff ((d ok2 `Seq.append` enc_unary n2) `Seq.append` s2);
    append_assoc_3 (d ok1) (enc_unary n1) s1;
    append_assoc_3 (d ok2) (enc_unary n2) s2;
    append_inj (d ok1) (enc_unary n1 `Seq.append` s1) (d ok2) (enc_unary n2 `Seq.append` s2);
    assert (Seq.index (d ok1) 0 == Seq.index (d ok2) 0);
    assert (Seq.index (d ok1) 0 == (if ok1 then 0uy else 1uy));
    assert (Seq.index (d ok2) 0 == (if ok2 then 0uy else 1uy));
    enc_unary_prefix_free n1 n2 s1 s2
  end

let asn1_id_enc_prefix_free (id1 id2: asn1_id_t) (s1 s2: bytes)
: Lemma
  (requires (asn1_id_enc id1 `Seq.append` s1 == asn1_id_enc id2 `Seq.append` s2))
  (ensures (id1 == id2 /\ s1 == s2))
= parse_asn1_identifier_U32_enc id1 s1;
  parse_asn1_identifier_U32_enc id2 s2;
  append_inj (asn1_id_enc id1) s1 (asn1_id_enc id2) s2

let enc_tlv_prefix_free (id1 id2: asn1_id_t) (ok1 ok2: bool) (c1 c2 s1 s2: bytes)
: Lemma
  (requires (enc_tlv id1 ok1 c1 `Seq.append` s1 == enc_tlv id2 ok2 c2 `Seq.append` s2))
  (ensures (id1 == id2 /\ ok1 == ok2 /\ c1 == c2 /\ s1 == s2))
= let h1 = enc_hdr ok1 (Seq.length c1) in
  let h2 = enc_hdr ok2 (Seq.length c2) in
  append_assoc_3 (asn1_id_enc id1) (h1 `Seq.append` c1) s1;
  append_assoc_3 (asn1_id_enc id2) (h2 `Seq.append` c2) s2;
  asn1_id_enc_prefix_free id1 id2 ((h1 `Seq.append` c1) `Seq.append` s1) ((h2 `Seq.append` c2) `Seq.append` s2);
  append_assoc_3 h1 c1 s1;
  append_assoc_3 h2 c2 s2;
  enc_hdr_prefix_free ok1 ok2 (Seq.length c1) (Seq.length c2) (c1 `Seq.append` s1) (c2 `Seq.append` s2);
  append_inj c1 s1 c2 s2

#push-options "--fuel 0 --ifuel 1"
private
let asn1_id_enc_length_pos (id: asn1_id_t)
: Lemma (Seq.length (asn1_id_enc id) > 0)
= let MK_ASN1_ID c f n = id in
  if U32.v n < 31
  then assert (Seq.length (asn1_id_enc id) == 1)
  else assert (Seq.length (asn1_id_enc id) == 1 + Seq.length (enc_long n))

private
let enc_tlv_length_pos (id: asn1_id_t) (ok: bool) (c: bytes)
: Lemma (Seq.length (enc_tlv id ok c) > 0)
= asn1_id_enc_length_pos id;
  Seq.lemma_len_append (enc_hdr ok (Seq.length c)) c;
  Seq.lemma_len_append (asn1_id_enc id) (enc_hdr ok (Seq.length c) `Seq.append` c)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let asn1_value_enc_nonempty (v: asn1_value)
: Lemma (Seq.length (asn1_value_enc v) > 0)
= match v with
  | ASN1_VALUE_PRIMITIVE id b -> enc_tlv_length_pos id (PRIMITIVE? id.f) b
  | ASN1_VALUE_CONSTRUCTED id l -> enc_tlv_length_pos id (CONSTRUCTED? id.f) (asn1_value_list_enc l)
#pop-options

let rec asn1_value_enc_prefix_free (v1 v2: asn1_value) (s1 s2: bytes)
: Lemma
  (requires (asn1_value_enc v1 `Seq.append` s1 == asn1_value_enc v2 `Seq.append` s2))
  (ensures (v1 == v2 /\ s1 == s2))
  (decreases v1)
= match v1, v2 with
  | ASN1_VALUE_PRIMITIVE id1 b1, ASN1_VALUE_PRIMITIVE id2 b2 ->
    enc_tlv_prefix_free id1 id2 (PRIMITIVE? id1.f) (PRIMITIVE? id2.f) b1 b2 s1 s2
  | ASN1_VALUE_CONSTRUCTED id1 l1, ASN1_VALUE_CONSTRUCTED id2 l2 ->
    enc_tlv_prefix_free id1 id2 (CONSTRUCTED? id1.f) (CONSTRUCTED? id2.f) (asn1_value_list_enc l1) (asn1_value_list_enc l2) s1 s2;
    asn1_value_list_enc_inj l1 l2
  | ASN1_VALUE_PRIMITIVE id1 b1, ASN1_VALUE_CONSTRUCTED id2 l2 ->
    enc_tlv_prefix_free id1 id2 (PRIMITIVE? id1.f) (CONSTRUCTED? id2.f) b1 (asn1_value_list_enc l2) s1 s2
  | ASN1_VALUE_CONSTRUCTED id1 l1, ASN1_VALUE_PRIMITIVE id2 b2 ->
    enc_tlv_prefix_free id1 id2 (CONSTRUCTED? id1.f) (PRIMITIVE? id2.f) (asn1_value_list_enc l1) b2 s1 s2

and asn1_value_list_enc_inj (l1 l2: list asn1_value)
: Lemma
  (requires (asn1_value_list_enc l1 == asn1_value_list_enc l2))
  (ensures (l1 == l2))
  (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | [], v :: _ | v :: _, [] -> asn1_value_enc_nonempty v
  | v1 :: q1, v2 :: q2 ->
    asn1_value_enc_prefix_free v1 v2 (asn1_value_list_enc q1) (asn1_value_list_enc q2);
    asn1_value_list_enc_inj q1 q2

let asn1_value_enc_inj (v1 v2: asn1_value)
: Lemma
  (requires (asn1_value_enc v1 == asn1_value_enc v2))
  (ensures (v1 == v2))
= Seq.append_empty_r (asn1_value_enc v1);
  Seq.append_empty_r (asn1_value_enc v2);
  asn1_value_enc_prefix_free v1 v2 Seq.empty Seq.empty
