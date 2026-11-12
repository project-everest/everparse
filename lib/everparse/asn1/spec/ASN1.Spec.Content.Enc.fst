module ASN1.Spec.Content.Enc

(* Total encoders for the contents of ASN.1 terminal types (other than
   prefixed terminals, which are TLVs handled in ASN1.Spec.ToValue), and
   their correctness with respect to the content parsers
   `asn1_terminal_as_parser` *)

open ASN1.Base

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.Int
open LowParse.Tot.List
open LowParse.Tot.SeqBytes

open ASN1.Spec.IdentifierU32
open ASN1.Spec.IdentifierU32.Enc
open ASN1.Spec.Content.BOOLEAN
open ASN1.Spec.Content.INTEGER
open ASN1.Spec.Content.BITSTRING
open ASN1.Spec.Content.OIDU32
open ASN1.Spec.Interpreter

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module Cast = FStar.Int.Cast

(* Correctness of an encoder with respect to a parser *)

let enc_correct (#k: parser_kind) (#t: Type) (p: parser k t) (f: t -> Tot bytes) : prop =
  forall (x: t) . parse p (f x) == Some (x, Seq.length (f x))

(* With any suffix: for strong parsers *)
let enc_correct_prefix (#k: parser_kind) (#t: Type) (p: parser k t) (f: t -> Tot bytes) : prop =
  forall (x: t) (s: bytes) . parse p (f x `Seq.append` s) == Some (x, Seq.length (f x))

(* The bytes consumed by a parser are the encoding of the parsed value *)
let enc_consumed
  (#k: parser_kind) (#t: Type) (p: parser k t) (f: t -> Tot bytes) (b: bytes)
: Lemma
  (requires (enc_correct p f /\ k.parser_kind_injective == true))
  (ensures (match parse p b with
    | Some (x, n) -> Seq.slice b 0 n == f x
    | None -> True))
= match parse p b with
  | Some (x, n) ->
    let e = f x in
    parse_injective #k p b e;
    Seq.lemma_eq_elim (Seq.slice e 0 (Seq.length e)) e
  | None -> ()

(* Lists *)

let rec list_enc (#t: Type) (f: t -> Tot bytes) (l: list t) : Tot bytes (decreases l) =
  match l with
  | [] -> Seq.empty
  | a :: q -> f a `Seq.append` list_enc f q

let rec parse_list_enc
  (#k: parser_kind) (#t: Type) (p: parser k t) (f: t -> Tot bytes) (l: list t)
: Lemma
  (requires (enc_correct_prefix p f /\ (forall (x: t) . Seq.length (f x) > 0)))
  (ensures (parse (parse_list p) (list_enc f l) == Some (l, Seq.length (list_enc f l))))
  (decreases l)
= let b = list_enc f l in
  tot_parse_list_eq p b;
  match l with
  | [] -> ()
  | a :: q ->
    parse_list_enc p f q;
    assert (parse p (f a `Seq.append` list_enc f q) == Some (a, Seq.length (f a)));
    Seq.lemma_eq_elim (Seq.slice b (Seq.length (f a)) (Seq.length b)) (list_enc f q)

(* Single bytes *)

let byte_enc (#f: U8.t -> Tot bool) (x: parse_filter_refine f) : Tot bytes = Seq.create 1 x

let parse_u8_filter_enc (f: U8.t -> Tot bool) (x: parse_filter_refine f) (s: bytes)
: Lemma (parse (parse_u8 `parse_filter` f) (byte_enc x `Seq.append` s) == Some (x, 1))
= let b = byte_enc x `Seq.append` s in
  parse_filter_eq parse_u8 f b;
  parse_u8_spec b;
  parse_u8_spec' b;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  assert (Seq.index b 0 == x)

let parse_char_list_enc (f: U8.t -> Tot bool) (l: list (parse_filter_refine f))
: Lemma (parse (parse_list (parse_u8 `parse_filter` f)) (list_enc byte_enc l) == Some (l, Seq.length (list_enc byte_enc l)))
= Classical.forall_intro_2 (parse_u8_filter_enc f);
  parse_list_enc (parse_u8 `parse_filter` f) byte_enc l

(* Byte sequences *)

let parse_seq_all_bytes_filter_enc (f: bytes -> Tot bool) (x: parse_filter_refine f)
: Lemma (parse (parse_seq_all_bytes `parse_filter` f) x == Some (x, Seq.length x))
= parse_filter_eq parse_seq_all_bytes f x

(* Base-128 subidentifiers (X.690 8.19.2), for OBJECT IDENTIFIER and
   RELATIVE-OID *)

let enc_arc (v: U32.t) : Tot bytes =
  if U32.v v < 128
  then Seq.create 1 (Cast.uint32_to_uint8 v)
  else enc_long v

let enc_arc_nonempty (v: U32.t) : Lemma (Seq.length (enc_arc v) > 0) = ()

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let parse_head_alt_step
  (x: byte { U8.v x >= 128 /\ U8.v x <> 128 })
  (rest: bytes)
: Lemma
  (ensures (
    initialize_partial_state_spec (U8.sub x 128uy);
    parse_asn1_identifier_loop_inj 0 (initialize_partial_state (U8.sub x 128uy));
    let r1 = parse (parse_asn1_identifier_head_alt x) rest in
    let r2 = parse (parse_u8 `and_then` parse_asn1_identifier_loop 0 (initialize_partial_state (U8.sub x 128uy))) rest in
    (Some? r1 <==> Some? r2) /\
    (Some? r1 ==> (U32.v (fst (Some?.v r1)) == U32.v (fst (Some?.v r2)) /\ snd (Some?.v r1) == snd (Some?.v r2)))
  ))
= initialize_partial_state_spec (U8.sub x 128uy);
  parse_asn1_identifier_loop_inj 0 (initialize_partial_state (U8.sub x 128uy));
  assert (parse (parse_asn1_identifier_head_alt x) rest == parse (parse_cast
        U32.t
        (fun y -> 0 < U32.v y /\ partial_state_prefixr (initialize_partial_state (U8.sub x 128uy)) y)
        (fun _ -> True)
        (fun _ -> ())
        (parse_asn1_identifier_head' (initialize_partial_state (U8.sub x 128uy)))) rest);
  assert (Some? (parse (parse_asn1_identifier_head_alt x) rest) <==> Some? (parse (parse_cast
        U32.t
        (fun y -> 0 < U32.v y /\ partial_state_prefixr (initialize_partial_state (U8.sub x 128uy)) y)
        (fun _ -> True)
        (fun _ -> ())
        (parse_asn1_identifier_head' (initialize_partial_state (U8.sub x 128uy)))) rest));
  parse_cast_eq
        U32.t
        (fun y -> 0 < U32.v y /\ partial_state_prefixr (initialize_partial_state (U8.sub x 128uy)) y)
        (fun _ -> True)
        (fun _ -> ())
        (parse_asn1_identifier_head' (initialize_partial_state (U8.sub x 128uy))) rest;
  assert (parse (parse_asn1_identifier_head' (initialize_partial_state (U8.sub x 128uy))) rest == parse (parse_u8 `and_then` parse_asn1_identifier_loop 0 (initialize_partial_state (U8.sub x 128uy))) rest) by (
    FStar.Tactics.norm [delta_only [`%parse_asn1_identifier_head'; `%weaken; `%tot_weaken; `%coerce_to_tot_bare_parser]; zeta; iota];
    FStar.Tactics.smt ()
  )

let parse_arc_enc
  (v: U32.t)
  (suffix: bytes)
: Lemma
  (parse parse_asn1_identifier_U32_alt (enc_arc v `Seq.append` suffix) == Some (v, Seq.length (enc_arc v)))
= lemma_parse_asn1_identifier_head_alt_inj ();
  assert_norm (pow2 8 == 256);
  assert (parse parse_asn1_identifier_U32_alt (enc_arc v `Seq.append` suffix) == parse (parse_u8 `and_then` parse_asn1_identifier_head_alt) (enc_arc v `Seq.append` suffix));
  if U32.v v < 128
  then begin
    let x = Cast.uint32_to_uint8 v in
    FStar.Math.Lemmas.small_mod (U32.v v) (pow2 8);
    Seq.lemma_eq_elim (enc_arc v `Seq.append` suffix) (Seq.cons x suffix);
    parse_u8_and_then_cons parse_asn1_identifier_head_alt x suffix;
    U32.v_inj (Cast.uint8_to_uint32 x) v
  end else begin
    id_digit_first v;
    if id_bound v = 0 then id_digit_last v
    else begin
      let x = U8.uint_to_t (id_digit v 0 + 128) in
      Seq.append_cons x (enc_tail v 0) suffix;
      Seq.lemma_eq_elim (enc_arc v `Seq.append` suffix) (Seq.cons x (enc_tail v 0 `Seq.append` suffix));
      parse_u8_and_then_cons parse_asn1_identifier_head_alt x (enc_tail v 0 `Seq.append` suffix);
      parse_head_alt_step x (enc_tail v 0 `Seq.append` suffix);
      initialize_partial_state_spec (U8.sub x 128uy);
      U32.v_inj (initialize_partial_state (U8.sub x 128uy)) (partial_state_prefixf v 0);
      parse_loop_state_eq 0 (initialize_partial_state (U8.sub x 128uy)) (partial_state_prefixf v 0) (enc_tail v 0 `Seq.append` suffix);
      parse_loop_enc_tail 0 v suffix;
      let r = parse parse_asn1_identifier_U32_alt (enc_arc v `Seq.append` suffix) in
      assert (Some? r);
      U32.v_inj (fst (Some?.v r)) v
    end
  end
#pop-options

let parse_arcs_enc (l: list U32.t)
: Lemma (parse parse_asn1_OIDU32_tail (list_enc enc_arc l) == Some (l, Seq.length (list_enc enc_arc l)))
= Classical.forall_intro_2 parse_arc_enc;
  Classical.forall_intro enc_arc_nonempty;
  parse_list_enc parse_asn1_identifier_U32_alt enc_arc l

let oid_head (l: asn1_oid_t) : Tot U32.t =
  match l with
  | x :: y :: _ -> U32.uint_to_t (40 * U32.v x + U32.v y)

let oid_enc (l: asn1_oid_t) : Tot bytes =
  match l with
  | _ :: _ :: tl -> enc_arc (oid_head l) `Seq.append` list_enc enc_arc tl

private
let synth_OIDU32_oid_head (l: asn1_oid_t)
: Lemma (match l with _ :: _ :: tl -> synth_OIDU32 (oid_head l, tl) == l)
= let x :: y :: tl = l in
  assert (U32.v (oid_head l) == 40 * U32.v x + U32.v y);
  if U32.v x = 0 then ()
  else if U32.v x = 1 then ()
  else ()

let parse_oid_enc (l: asn1_oid_t)
: Lemma (parse parse_asn1_OIDU32 (oid_enc l) == Some (l, Seq.length (oid_enc l)))
= let _ :: _ :: tl = l in
  let h = oid_head l in
  let b = oid_enc l in
  lemma_synth_OIDU32_inj ();
  parse_synth_eq (parse_asn1_identifier_U32_alt `nondep_then` parse_asn1_OIDU32_tail) synth_OIDU32 b;
  nondep_then_eq parse_asn1_identifier_U32_alt parse_asn1_OIDU32_tail b;
  parse_arc_enc h (list_enc enc_arc tl);
  Seq.lemma_eq_elim (Seq.slice b (Seq.length (enc_arc h)) (Seq.length b)) (list_enc enc_arc tl);
  parse_arcs_enc tl;
  synth_OIDU32_oid_head l

let parse_relative_oid_enc (l: asn1_relative_oid_t)
: Lemma (parse parse_asn1_RELATIVE_OIDU32 (list_enc enc_arc l) == Some (l, Seq.length (list_enc enc_arc l)))
= parse_filter_eq parse_asn1_OIDU32_tail asn1_relative_oid_wf (list_enc enc_arc l);
  parse_arcs_enc l

(* BOOLEAN, INTEGER, BIT STRING *)

let boolean_enc (x: bool) : Tot bytes = Seq.create 1 (if x then 0xFFuy else 0x00uy)

let parse_boolean_enc (x: bool)
: Lemma (parse parse_asn1_boolean (boolean_enc x) == Some (x, 1))
= let b = boolean_enc x in
  lemma_parse_asn1_boolean_unfold b;
  parse_u8_spec b;
  parse_u8_spec' b;
  parser_kind_prop_equiv parse_u8_kind parse_u8

(* The length is computed from `x` (`domain_intro_gen`), not by counting
   down from `bound` (`interval_elim`) as `serialize_untagged_bounded_integer`
   does, which would not be executable for `asn1_any_integer_bound`. *)
let integer_enc (bound: pos) (x: integer_in_interval bound) : Tot bytes =
  mk_bytes (domain_intro_gen x) x

let parse_integer_enc (bound: pos) (x: integer_in_interval bound)
: Lemma (parse (parse_untagged_bounded_integer bound) (integer_enc bound x) == Some (x, Seq.length (integer_enc bound x)))
= domain_unique (domain_intro_gen x) (interval_elim bound x) x;
  assert (integer_enc bound x == serialize (serialize_untagged_bounded_integer bound) x)

(* An INTEGER key literal is its own content encoding *)
let integer_enc_of_lit (bound: pos) (l: asn1_int_lit bound)
: Lemma (Seq.seq_of_list l == integer_enc bound (int_of_lit bound l))
= let b = Seq.seq_of_list l in
  let x = int_of_lit bound l in
  int_lit_valid bound l;
  parse_integer_enc bound x;
  assert (parse (parse_untagged_bounded_integer bound) b == Some (x, Seq.length b));
  LowParse.Spec.Base.parse_injective #(parse_untagged_bounded_integer_kind bound) (parse_untagged_bounded_integer bound) b (integer_enc bound x);
  Seq.lemma_eq_elim b (Seq.slice b 0 (Seq.length b));
  Seq.lemma_eq_elim (integer_enc bound x) (Seq.slice (integer_enc bound x) 0 (Seq.length (integer_enc bound x)))

let bitstring_enc (x: asn1_bitstring_t) : Tot bytes =
  let BYTES_WITH_UNUSEDBITS u b = x in
  Seq.cons u b

#push-options "--z3rlimit 32"
let parse_bitstring_enc (x: asn1_bitstring_t)
: Lemma (parse parse_asn1_bitstring (bitstring_enc x) == Some (x, Seq.length (bitstring_enc x)))
= let BYTES_WITH_UNUSEDBITS u b = x in
  let e = bitstring_enc x in
  parse_asn1_bitstring_payload_cases_injective ();
  and_then_eq (parse_u8 `parse_filter` filter_asn1_bitstring_unused) parse_asn1_bitstring_payload e;
  Seq.lemma_eq_elim e (byte_enc #filter_asn1_bitstring_unused u `Seq.append` b);
  parse_u8_filter_enc filter_asn1_bitstring_unused u b;
  Seq.lemma_eq_elim (Seq.slice e 1 (Seq.length e)) b;
  parse_synth_eq (parse_seq_all_bytes `parse_filter` (filter_asn1_bitstring_payload u)) (synth_asn1_bitstring u) b;
  parse_filter_eq parse_seq_all_bytes (filter_asn1_bitstring_payload u) b
#pop-options

(* All non-prefixed terminals *)

let leaf_k = (k: asn1_terminal_k { not (ASN1_PREFIXED_TERMINAL? k) })

let leaf_enc (k: leaf_k) (x: asn1_terminal_t k) : Tot bytes =
  match k with
  | ASN1_BOOLEAN -> boolean_enc x
  | ASN1_INTEGER bound -> integer_enc bound x
  | ASN1_BITSTRING -> bitstring_enc x
  | ASN1_PRINTABLESTRING -> let x : asn1_printablestring_t = x in list_enc (byte_enc #is_printable_char) x
  | ASN1_IA5STRING -> let x : asn1_ia5string_t = x in list_enc (byte_enc #is_ia5_char) x
  | ASN1_VISIBLESTRING -> let x : asn1_visiblestring_t = x in list_enc (byte_enc #is_visible_char) x
  | ASN1_NUMERICSTRING -> let x : asn1_numericstring_t = x in list_enc (byte_enc #is_numeric_char) x
  | ASN1_NULL -> Seq.empty
  | ASN1_OID -> oid_enc x
  | ASN1_RELATIVE_OID -> list_enc enc_arc x
  | ASN1_OCTETSTRING
  | ASN1_UTF8STRING
  | ASN1_BMPSTRING
  | ASN1_UNIVERSALSTRING
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR
  | ASN1_OID_IRI
  | ASN1_RELATIVE_OID_IRI
  | ASN1_UTCTIME
  | ASN1_GENERALIZEDTIME
  | ASN1_DATE
  | ASN1_TIME_OF_DAY
  | ASN1_DATE_TIME -> (x <: bytes)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let parse_leaf_enc (k: leaf_k) (x: asn1_terminal_t k)
: Lemma (parse (asn1_terminal_as_parser k) (leaf_enc k x) == Some (x, Seq.length (leaf_enc k x)))
= match k with
  | ASN1_BOOLEAN -> parse_boolean_enc x
  | ASN1_INTEGER bound -> parse_integer_enc bound x
  | ASN1_BITSTRING -> parse_bitstring_enc x
  | ASN1_PRINTABLESTRING -> let x : asn1_printablestring_t = x in parse_char_list_enc is_printable_char x
  | ASN1_IA5STRING -> let x : asn1_ia5string_t = x in parse_char_list_enc is_ia5_char x
  | ASN1_VISIBLESTRING -> let x : asn1_visiblestring_t = x in parse_char_list_enc is_visible_char x
  | ASN1_NUMERICSTRING -> let x : asn1_numericstring_t = x in parse_char_list_enc is_numeric_char x
  | ASN1_NULL -> ()
  | ASN1_OID -> parse_oid_enc x
  | ASN1_RELATIVE_OID -> parse_relative_oid_enc x
  | ASN1_OCTETSTRING
  | ASN1_TELETEXSTRING
  | ASN1_VIDEOTEXSTRING
  | ASN1_GRAPHICSTRING
  | ASN1_GENERALSTRING
  | ASN1_OBJECTDESCRIPTOR -> ()
  | ASN1_UTF8STRING -> parse_seq_all_bytes_filter_enc LowParse.Spec.UTF8.correct x
  | ASN1_BMPSTRING -> parse_seq_all_bytes_filter_enc is_valid_bmp x
  | ASN1_UNIVERSALSTRING -> parse_seq_all_bytes_filter_enc is_valid_universal x
  | ASN1_OID_IRI -> parse_seq_all_bytes_filter_enc ASN1.Spec.IRI.is_valid_oid_iri x
  | ASN1_RELATIVE_OID_IRI -> parse_seq_all_bytes_filter_enc ASN1.Spec.IRI.is_valid_relative_oid_iri x
  | ASN1_UTCTIME -> parse_seq_all_bytes_filter_enc ASN1.Spec.Time.is_valid_ASN1UTCTIME x
  | ASN1_GENERALIZEDTIME -> parse_seq_all_bytes_filter_enc ASN1.Spec.Time.is_valid_ASN1GENERALIZEDTIME x
  | ASN1_DATE -> parse_seq_all_bytes_filter_enc ASN1.Spec.Time.is_valid_ASN1DATE x
  | ASN1_TIME_OF_DAY -> parse_seq_all_bytes_filter_enc ASN1.Spec.Time.is_valid_ASN1TIMEOFDAY x
  | ASN1_DATE_TIME -> parse_seq_all_bytes_filter_enc ASN1.Spec.Time.is_valid_ASN1DATETIME x
#pop-options

let leaf_enc_correct (k: leaf_k)
: Lemma (enc_correct (asn1_terminal_as_parser k) (leaf_enc k))
= Classical.forall_intro (parse_leaf_enc k)

let leaf_enc_consumed (k: leaf_k) (b: bytes)
: Lemma (match parse (asn1_terminal_as_parser k) b with
    | Some (x, n) -> Seq.slice b 0 n == leaf_enc k x
    | None -> True)
= leaf_enc_correct k;
  enc_consumed (asn1_terminal_as_parser k) (leaf_enc k) b

let leaf_enc_inj (k: leaf_k) (x1 x2: asn1_terminal_t k)
: Lemma (requires (leaf_enc k x1 == leaf_enc k x2)) (ensures (x1 == x2))
= parse_leaf_enc k x1;
  parse_leaf_enc k x2
