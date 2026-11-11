module ASN1.Pulse.ParseSequence.Lemmas

(* Value-level lemmas for the zero-copy SEQUENCE parser:

   - every typed parser is its identifier followed by its twin;
   - every twin consumes exactly the length header and the contents it
     announces, so that the extent of a present item is known from its
     identifier and length header;
   - the SEQUENCE machine on validated bytes splits into a present item
     followed by the remaining items, or an absent item. *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.VLGen
open LowParse.Tot.Defaultable

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.LengthU32
open ASN1.Spec.Value
open ASN1.Spec.Value.Enc
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.Interpreter

module RV = LowParse.Spec.RecursiveVLGen
module U32 = FStar.UInt32
module Seq = FStar.Seq
module SB = LowParse.Spec.Base
module SC = LowParse.Spec.Combinators
module C = ASN1.Spec.Conformance
module TS = ASN1.Spec.ToValue.Sound
module ILC = ASN1.Pulse.ILC
module Sq = ASN1.Pulse.Sequence
module Co = ASN1.Pulse.Constructed
module I = ASN1.Pulse.Interpreter
module P = ASN1.Pulse.Parse

(* Identifier, then twin *)

let id_then_v (#t: Type) (fp: asn1_id_t -> parser asn1_strong_parser_kind t) (b: bytes) : GTot (option (t & consumed_length b)) =
  match parse parse_asn1_identifier_U32 b with
  | None -> None
  | Some (id, c1) ->
    match parse (fp id) (Seq.slice b c1 (Seq.length b)) with
    | None -> None
    | Some (x, c2) -> Some (x, c1 + c2)

(* The proofs below are brittle when the SMT solver must re-derive these
   facts inside large contexts (e.g. after `parse_rec_vlgen_eq`): they used
   to time out depending on the Z3 seed or platform. Hence these small
   helper lemmas, each proven in a clean context. *)

let id_then_v_some (#t: Type) (fp: asn1_id_t -> parser asn1_strong_parser_kind t) (b: bytes)
  (id: asn1_id_t) (c1: consumed_length b) (x: t) (c2: consumed_length (Seq.slice b c1 (Seq.length b)))
: Lemma
  (requires (
    parse parse_asn1_identifier_U32 b == Some (id, c1) /\
    parse (fp id) (Seq.slice b c1 (Seq.length b)) == Some (x, c2)))
  (ensures (id_then_v fp b == Some (x, c1 + c2)))
= ()

let add_assoc (a b c: nat) : Lemma (a + b + c == a + (b + c)) = ()

let eq_opt_pair (#t: Type) (b: bytes) (r1 r2: option (t & consumed_length b))
: Lemma
  (requires (match r1, r2 with
    | None, None -> True
    | Some (x1, n1), Some (x2, n2) -> x1 == x2 /\ (n1 <: nat) == n2
    | _ -> False))
  (ensures (r1 == r2))
= ()

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let any_id_then (b: bytes)
: Lemma (parse parse_asn1_value b == id_then_v parse_asn1_value_twin b)
= RV.parse_rec_vlgen_eq asn1_value_param b;
  parse_any_identifier_consumed b;
  parser_kind_prop_equiv asn1_any_identifier_kind parse_asn1_any_identifier;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    if asn1_any_id_valid id then begin
      C.twin_eq id b1;
      match parse parse_asn1_length_u32_t b1 with
      | None -> assert (RV.rec_vlgen_header asn1_value_param b == None)
      | Some (len, sz) ->
        assert (RV.rec_vlgen_header asn1_value_param b == Some (id, c1 + sz, U32.v len));
        if Seq.length b1 < sz + U32.v len then ()
        else begin
          C.slice_slice_3 b c1 sz (U32.v len);
          let ct = Seq.slice b (c1 + sz) (c1 + sz + U32.v len) in
          match parse (RV.rec_vlgen_body asn1_value_param pv id) ct with
          | None -> ()
          | Some (x, c) ->
            if c = U32.v len then begin
              let n : consumed_length b = c1 + sz + U32.v len in
              let r : option (asn1_value & consumed_length b) = Some (synth_asn1_value_twin id x, n) in
              assert (synth_asn1_value_twin id x == asn1_value_param.RV.synth_ (| id, x |));
              assert (parse pv b == r);
              let n1 : consumed_length b1 = sz + U32.v len in
              let r1 : option (asn1_value & consumed_length b1) = Some (synth_asn1_value_twin id x, n1) in
              assert (parse (parse_asn1_value_twin id) b1 == r1);
              id_then_v_some parse_asn1_value_twin b id c1 (synth_asn1_value_twin id x) n1;
              add_assoc c1 sz (U32.v len);
              eq_opt_pair b (parse parse_asn1_value b) (id_then_v parse_asn1_value_twin b)
            end
        end
    end
    else assert (parse parse_asn1_any_identifier b == None)
#pop-options

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let choice_id_then (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (b: bytes)
: Lemma (parse (asn1_as_parser (ASN1_CHOICE_ILC lc pf)) b == id_then_v (snd (asn1_as_parser_twin (ASN1_CHOICE_ILC lc pf))) b)
= let k = ASN1_CHOICE_ILC lc pf in
  let lp = asn1_lc_as_parser lc in
  parse_tagged_union_eq parse_asn1_identifier_U32 (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_strong_payload_parser lp) b;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, c1) ->
    assert (snd (asn1_as_parser_twin k) id == make_asn1_choice_parser_twin_cases lc pf k lp id);
    SC.parse_synth_eq #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser lp id) (SC.synth_tagged_union_data (project_tags lp) id) (Seq.slice b c1 (Seq.length b))
#pop-options

let k_id_then (#s: _) (k: asn1_k s) (b: bytes)
: Lemma (parse (asn1_as_parser k) b == id_then_v (snd (asn1_as_parser_twin k)) b)
= match k with
  | ASN1_ILC id k' -> ILC.ilc_eq id (asn1_content_as_parser k') b
  | ASN1_CHOICE_ILC lc pf -> choice_id_then lc pf b
  | ASN1_ANY_ILC -> any_id_then b

(* Twins consume their length header and contents *)

let lc_size (b: bytes) : GTot (option nat) =
  match parse parse_asn1_length_u32_t b with
  | None -> None
  | Some (len, c2) -> Some (c2 + U32.v len)

let tlv_size (b: bytes) : GTot (option nat) =
  match parse parse_asn1_identifier_U32 b with
  | None -> None
  | Some (_, c1) ->
    match lc_size (Seq.slice b c1 (Seq.length b)) with
    | None -> None
    | Some n -> Some (c1 + n)

let lc_shaped (#k: parser_kind) (#t: Type) (p: parser k t) : prop =
  forall b . match Sq.consumed #k #t p b with
  | Some n -> lc_size b == Some n
  | None -> True

let lc_lc_shaped (#ack: asn1_content_k) (p: asn1_weak_parser (asn1_content_t ack))
: Lemma (lc_shaped (parse_asn1_LC p))
= Classical.forall_intro (C.vlgen_eq p)

#push-options "--fuel 1 --ifuel 1"
let rec lc_payload_shaped (lc: list (asn1_id_t & asn1_content_k)) (id: asn1_id_t) (b: bytes)
: Lemma (ensures (match Sq.consumed #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) b with
    | Some n -> lc_size b == Some n
    | None -> True))
  (decreases lc)
= match lc with
  | [] ->
    assert_norm (asn1_lc_as_parser [] == []);
    Co.choice_payload_nil id b
  | (id', ck) :: tl ->
    Co.asn1_choice_payload_cons id' ck tl id b;
    if id = id'
    then C.vlgen_eq (asn1_content_as_parser ck) b
    else lc_payload_shaped tl id b
#pop-options

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let k_twin_shaped' (#s: _) (k: asn1_k s) (id: asn1_id_t) (b: bytes)
: Lemma (match Sq.consumed #asn1_strong_parser_kind (snd (asn1_as_parser_twin k) id) b with
    | Some n -> lc_size b == Some n
    | None -> True)
= match k with
  | ASN1_ILC id0 k' -> if id = id0 then C.vlgen_eq (asn1_content_as_parser k') b
  | ASN1_CHOICE_ILC lc pf ->
    Co.asn1_choice_twin_consumed lc pf id b;
    lc_payload_shaped lc id b
  | ASN1_ANY_ILC ->
    if asn1_any_id_valid id then C.twin_eq id b
#pop-options

let k_twin_shaped (#s: _) (k: asn1_k s) (id: asn1_id_t)
: Lemma (lc_shaped (snd (asn1_as_parser_twin k) id))
= Classical.forall_intro (k_twin_shaped' k id)

(* Sequence items *)

let item_shaped (hd: gen_decorated_parser_twin) : prop =
  forall id . lc_shaped (parse_asn1_sequence_item_twin hd id)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let dec_shaped' (#s: _) (#d: _) (dk: asn1_decorated_k s d) (id: asn1_id_t) (b: bytes)
: Lemma (match Sq.consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin (I.twin_of dk) id) b with
    | Some n -> lc_size b == Some n
    | None -> True)
= let item = I.twin_of dk in
  match dk with
  | ASN1_PLAIN_ILC k -> k_twin_shaped' k id b
  | ASN1_OPTION_ILC k ->
    k_twin_shaped' k id b;
    parse_synth_eq (Mkgendcparser?.fp item id) Some b
  | ASN1_DEFAULT_TERMINAL id0 #k defv ->
    let fp = Mkgendcparser?.fp item in
    parse_synth_eq ((fp id) `parse_filter` (defaultv_filter (key_of_lit k defv))) (defaultv_synth (key_of_lit k defv)) b;
    parse_filter_eq (fp id) (defaultv_filter (key_of_lit k defv)) b;
    if id = id0 then C.vlgen_eq (asn1_terminal_as_parser k) b
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv ->
    let fp = Mkgendcparser?.fp item in
    let d = Mkgendcparser?.d item in
    parse_synth_eq (((fp id) `parse_filter` (restriction_pred r)) `parse_filter` (defaultv_filter #(asn1_decorated_pure_t d) (key_of_lit k defv))) (defaultv_synth #(asn1_decorated_pure_t d) (key_of_lit k defv)) b;
    parse_filter_eq ((fp id) `parse_filter` (restriction_pred r)) (defaultv_filter #(asn1_decorated_pure_t d) (key_of_lit k defv)) b;
    parse_filter_eq (fp id) (restriction_pred r) b;
    if id = id0 then C.vlgen_eq (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) b
#pop-options

let dec_shaped (#s: _) (#d: _) (dk: asn1_decorated_k s d)
: Lemma (item_shaped (I.twin_of dk))
= Classical.forall_intro_2 (dec_shaped' dk)

(* The value of a present item, parsed from its own bytes *)

let item_parsed (hd: gen_decorated_parser_twin) (w: bytes) (v: asn1_decorated_t (Mkgendcparser?.d hd)) : prop =
  match parse parse_asn1_identifier_U32 w with
  | None -> False
  | Some (id, c1) ->
    match parse (parse_asn1_sequence_item_twin hd id) (Seq.slice w c1 (Seq.length w)) with
    | None -> False
    | Some (v', n) -> v' == v /\ c1 + n == Seq.length w

let seq_parsed (its: list gen_decorated_parser_twin) (w: bytes) (v: asn1_sequence_t (List.Tot.map Mkgendcparser?.d its)) : prop =
  P.parsed #asn1_weak_parser_kind (make_asn1_sequence_parser' its None) w v

let absent (hd: gen_decorated_parser_twin) (v: asn1_decorated_t (Mkgendcparser?.d hd)) : prop =
  generate_defaultable_item hd == Some v

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let identifier_nonempty (b: bytes)
: Lemma (match parse parse_asn1_identifier_U32 b with
    | Some (_, c) -> c > 0
    | None -> True)
= ASN1.Spec.IdentifierU32.Enc.parse_asn1_identifier_U32_consumed b;
  match parse parse_asn1_identifier_U32 b with
  | Some (id, c) ->
    let MK_ASN1_ID cl f n = id in
    assert (Seq.length (Seq.slice b 0 c) == c);
    assert (Seq.length (ASN1.Spec.IdentifierU32.Enc.asn1_id_enc id) >= 1)
  | None -> ()
#pop-options

(* The SEQUENCE machine, after an identifier, in state `Some id` *)

let parsed_shift (#t: Type) (r1: option (t & nat)) (r2: option (t & nat)) (c: nat) : prop =
  match r1, r2 with
  | None, None -> True
  | Some (v1, n1), Some (v2, n2) -> v1 == v2 /\ n1 == c + n2
  | _ -> False

let res_nat (#t: Type) (#b: bytes) (r: option (t & consumed_length b)) : Tot (option (t & nat)) =
  match r with
  | None -> None
  | Some (v, n) -> Some (v, n)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let seq_none_some (its: list gen_decorated_parser_twin { Cons? its }) (w: bytes)
: Lemma (match parse parse_asn1_identifier_U32 w with
    | None -> parse (make_asn1_sequence_parser' its None) w == None \/ Seq.length w == 0
    | Some (id, c1) ->
      parsed_shift (res_nat (parse (make_asn1_sequence_parser' its None) w)) (res_nat (parse (make_asn1_sequence_parser' its (Some id)) (Seq.slice w c1 (Seq.length w)))) c1)
= identifier_nonempty w;
  TS.seq'_veq its None w;
  TS.seq''_veq its None w;
  make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
  let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  and_then_eq (weaken k parse_asn1_identifier_U32) pbt w;
  match parse parse_asn1_identifier_U32 w with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice w c1 (Seq.length w) in
    TS.seq'_veq its (Some id) b1;
    TS.seq''_veq its (Some id) b1;
    and_then_eq (weaken k (parse_ret id)) pbt b1;
    Seq.lemma_eq_elim b1 (Seq.slice b1 0 (Seq.length b1))
#pop-options

(* Single item *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let seq_single (hd: gen_decorated_parser_twin) (w: bytes) (v: asn1_decorated_t (Mkgendcparser?.d hd))
: Lemma
  (requires (seq_parsed [hd] w v))
  (ensures (if Seq.length w = 0 then absent hd v else item_parsed hd w v))
= identifier_nonempty w;
  TS.seq'_veq [hd] None w;
  TS.seq''_veq [hd] None w;
  make_asn1_sequence_parser_body_twin_and_then_cases_injective [hd] make_asn1_sequence_parser';
  let pbt = make_asn1_sequence_parser_body_twin [hd] make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  and_then_eq (weaken k parse_asn1_identifier_U32) pbt w;
  match parse parse_asn1_identifier_U32 w with
  | None -> ()
  | Some (id, c1) ->
    TS.body_twin_veq_single hd id (Seq.slice w c1 (Seq.length w))
#pop-options

(* Two or more items *)

let seq_cons_post (hd hd': gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (w: bytes) (v1: asn1_decorated_t (Mkgendcparser?.d hd)) (v2: asn1_sequence_t (List.Tot.map Mkgendcparser?.d (hd' :: tl))) : prop =
  if Seq.length w = 0
  then absent hd v1 /\ seq_parsed (hd' :: tl) w v2
  else match parse parse_asn1_identifier_U32 w with
  | None -> False
  | Some (id, _) ->
    if Set.mem id (Sq.item_set hd)
    then (match tlv_size w with
      | None -> False
      | Some n -> n <= Seq.length w /\ item_parsed hd (Seq.slice w 0 n) v1 /\ seq_parsed (hd' :: tl) (Seq.slice w n (Seq.length w)) v2)
    else absent hd v1 /\ seq_parsed (hd' :: tl) w v2

let slice_prefix_slice (w: bytes) (c1 n2: nat)
: Lemma
  (requires (c1 + n2 <= Seq.length w))
  (ensures (
    let w' = Seq.slice w 0 (c1 + n2) in
    Seq.slice w' 0 c1 == Seq.slice w 0 c1 /\
    Seq.slice w' c1 (Seq.length w') == Seq.slice (Seq.slice w c1 (Seq.length w)) 0 n2))
= Seq.lemma_eq_elim (Seq.slice (Seq.slice w 0 (c1 + n2)) 0 c1) (Seq.slice w 0 c1);
  Seq.lemma_eq_elim (Seq.slice (Seq.slice w 0 (c1 + n2)) c1 (c1 + n2)) (Seq.slice (Seq.slice w c1 (Seq.length w)) 0 n2)

#push-options "--z3rlimit 20"
let item_parsed_prefix (hd: gen_decorated_parser_twin) (w: bytes) (v: asn1_decorated_t (Mkgendcparser?.d hd))
  (id: asn1_id_t) (c1: consumed_length w) (n2: consumed_length (Seq.slice w c1 (Seq.length w)))
: Lemma
  (requires (
    parse parse_asn1_identifier_U32 w == Some (id, c1) /\
    parse (parse_asn1_sequence_item_twin hd id) (Seq.slice w c1 (Seq.length w)) == Some (v, n2)))
  (ensures (
    c1 + n2 <= Seq.length w /\
    item_parsed hd (Seq.slice w 0 (c1 + n2)) v))
= let b1 = Seq.slice w c1 (Seq.length w) in
  slice_prefix_slice w c1 n2;
  parse_strong_prefix #asn1_strong_parser_kind parse_asn1_identifier_U32 w (Seq.slice w 0 (c1 + n2));
  parse_strong_prefix #asn1_strong_parser_kind (parse_asn1_sequence_item_twin hd id) b1 (Seq.slice b1 0 n2)
#pop-options

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let seq_cons_present (hd hd': gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (w: bytes) (v1: asn1_decorated_t (Mkgendcparser?.d hd)) (v2: asn1_sequence_t (List.Tot.map Mkgendcparser?.d (hd' :: tl)))
  (id: asn1_id_t) (c1: consumed_length w) (n2: consumed_length (Seq.slice w c1 (Seq.length w)))
: Lemma
  (requires (
    let b1 = Seq.slice w c1 (Seq.length w) in
    Seq.length w <> 0 /\
    item_shaped hd /\
    parse parse_asn1_identifier_U32 w == Some (id, c1) /\
    Set.mem id (Sq.item_set hd) /\
    parse (parse_asn1_sequence_item_twin hd id) b1 == Some (v1, n2) /\
    seq_parsed (hd' :: tl) (Seq.slice b1 n2 (Seq.length b1)) v2))
  (ensures (seq_cons_post hd hd' tl w v1 v2))
= let b1 = Seq.slice w c1 (Seq.length w) in
  let p1 = parse_asn1_sequence_item_twin hd id in
  assert (lc_shaped p1);
  assert (Sq.consumed #asn1_strong_parser_kind p1 b1 == Some n2);
  assert (tlv_size w == Some (c1 + n2));
  item_parsed_prefix hd w v1 id c1 n2;
  Seq.slice_slice w c1 (Seq.length w) n2 (Seq.length b1)
#pop-options

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let seq_cons (hd hd': gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (w: bytes) (v1: asn1_decorated_t (Mkgendcparser?.d hd)) (v2: asn1_sequence_t (List.Tot.map Mkgendcparser?.d (hd' :: tl)))
: Lemma
  (requires (seq_parsed (hd :: hd' :: tl) w (v1, v2) /\ item_shaped hd))
  (ensures (seq_cons_post hd hd' tl w v1 v2))
= let its = hd :: hd' :: tl in
  identifier_nonempty w;
  TS.seq'_veq its None w;
  TS.seq'_veq (hd' :: tl) None w;
  TS.seq''_veq its None w;
  make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
  let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  and_then_eq (weaken k parse_asn1_identifier_U32) pbt w;
  if Seq.length w = 0 then ()
  else match parse parse_asn1_identifier_U32 w with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice w c1 (Seq.length w) in
    TS.body_twin_veq_cons hd hd' tl id b1;
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    if Set.mem id s
    then begin
      let p1 = parse_asn1_sequence_item_twin hd id in
      let p2 = make_asn1_sequence_parser' (hd' :: tl) None in
      nondep_then_eq p1 p2 b1;
      assert (parse (pbt id) b1 == parse (p1 `nondep_then` p2) b1);
      assert (match parse (p1 `nondep_then` p2) b1 with Some (v, n) -> v == (v1, v2) /\ c1 + n == Seq.length w | None -> False);
      let Some (x1, n2) = parse p1 b1 in
      assert (x1 == v1);
      let b2 = Seq.slice b1 n2 (Seq.length b1) in
      let Some (x2, n3) = parse p2 b2 in
      assert (x2 == v2 /\ c1 + (n2 + n3) == Seq.length w);
      assert (n3 == Seq.length b2);
      seq_cons_present hd hd' tl w v1 v2 id c1 n2
    end
    else match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_parser' (hd' :: tl) (Some id) in
      nondep_then_eq p1 p2 b1;
      Seq.lemma_eq_elim b1 (Seq.slice b1 0 (Seq.length b1));
      seq_none_some (hd' :: tl) w
#pop-options

(* Present and absent items, per decorator *)

#push-options "--fuel 1 --ifuel 1"
let dec_plain (#s: _) (k: asn1_k s) (w: bytes) (v: asn1_t k)
: Lemma
  (requires (item_parsed (I.twin_of (ASN1_PLAIN_ILC k)) w v))
  (ensures (P.parsed #asn1_strong_parser_kind (asn1_as_parser k) w v))
= k_id_then k w;
  match parse parse_asn1_identifier_U32 w with
  | Some (id, c1) ->
    assert (parse_asn1_sequence_item_twin (I.twin_of (ASN1_PLAIN_ILC k)) id == snd (asn1_as_parser_twin k) id)

let dec_option (#s: _) (k: asn1_k s) (w: bytes) (v: option (asn1_t k))
: Lemma
  (requires (item_parsed (I.twin_of (ASN1_OPTION_ILC k)) w v))
  (ensures (Some? v /\ P.parsed #asn1_strong_parser_kind (asn1_as_parser k) w (Some?.v v)))
= k_id_then k w;
  match parse parse_asn1_identifier_U32 w with
  | Some (id, c1) ->
    assert (parse_asn1_sequence_item_twin (I.twin_of (ASN1_OPTION_ILC k)) id == (snd (asn1_as_parser_twin k) id `parse_synth` Some));
    parse_synth_eq (snd (asn1_as_parser_twin k) id) Some (Seq.slice w c1 (Seq.length w))

let dec_default (id0: asn1_id_t) (#k: asn1_terminal_k) (defv: asn1_key_lit k) (w: bytes) (v: default_tv (key_of_lit k defv))
: Lemma
  (requires (item_parsed (I.twin_of (ASN1_DEFAULT_TERMINAL id0 #k defv)) w v))
  (ensures (Nondefault? v /\ P.parsed #asn1_strong_parser_kind (parse_asn1_ILC id0 #(ASN1_TERMINAL k) (asn1_terminal_as_parser k)) w (Nondefault?.v' v)))
= let p = asn1_terminal_as_parser k in
  ILC.ilc_eq id0 #(ASN1_TERMINAL k) p w;
  match parse parse_asn1_identifier_U32 w with
  | Some (id, c1) ->
    let b1 = Seq.slice w c1 (Seq.length w) in
    let fp = parse_asn1_ILC_twin id0 #(ASN1_TERMINAL k) p in
    parse_synth_eq ((fp id) `parse_filter` (defaultv_filter (key_of_lit k defv))) (defaultv_synth (key_of_lit k defv)) b1;
    parse_filter_eq (fp id) (defaultv_filter (key_of_lit k defv)) b1

(* Quantified forms of parse_synth_eq / parse_filter_eq, to be called
   locally (not SMTPat lemmas, so as not to pollute dependent modules) *)
let parse_synth_eq_forall () : Lemma
  (forall (k: parser_kind) (t1 t2: Type0) (p1: parser k t1) (f2: t1 -> Tot t2) (b: bytes) .
    {:pattern (parse (parse_synth p1 f2) b)}
    (k.parser_kind_injective ==> synth_injective f2) ==>
    parse (parse_synth p1 f2) b == SC.parse_synth' #k p1 f2 b)
= introduce forall (k: parser_kind) (t1 t2: Type0) (p1: parser k t1) (f2: t1 -> Tot t2) (b: bytes) .
    (k.parser_kind_injective ==> synth_injective f2) ==>
    parse (parse_synth p1 f2) b == SC.parse_synth' #k p1 f2 b
  with introduce _ ==> _
  with parse_synth_eq p1 f2 b

let parse_filter_eq_forall () : Lemma
  (forall (k: parser_kind) (t: Type0) (p: parser k t) (f: t -> Tot bool) (b: bytes) .
    {:pattern (parse (parse_filter p f) b)}
    parse (parse_filter p f) b == (match parse p b with
    | None -> None
    | Some (x, c) -> if f x then Some (x, c) else None))
= introduce forall (k: parser_kind) (t: Type0) (p: parser k t) (f: t -> Tot bool) (b: bytes) .
    parse (parse_filter p f) b == (match parse p b with
    | None -> None
    | Some (x, c) -> if f x then Some (x, c) else None)
  with parse_filter_eq p f b

#push-options "--z3rlimit 32"
let dec_default_restricted (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_key_lit k { restriction_pred r (key_of_lit k defv) }) (w: bytes) (v: default_tv #(parse_filter_refine (restriction_pred r)) (key_of_lit k defv))
: Lemma
  (requires (item_parsed (I.twin_of (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)) w v))
  (ensures (Nondefault? v /\ P.parsed #asn1_strong_parser_kind (parse_asn1_ILC id0 #(ASN1_RESTRICTED_TERMINAL k r) (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r))) w (Nondefault?.v' v)))
= let dv : parse_filter_refine (restriction_pred r) = key_of_lit k defv in
  let p : asn1_weak_parser (parse_filter_refine (restriction_pred r)) = weaken _ ((asn1_terminal_as_parser k) `parse_filter` (restriction_pred r)) in
  assert (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r) == weaken _ ((asn1_terminal_as_parser k) `parse_filter` (restriction_pred r))) by (FStar.Tactics.V2.norm [delta_only [`%asn1_content_as_parser; `%asn1_content_t]; iota; zeta]; FStar.Tactics.V2.trefl ());
  ILC.ilc_eq id0 #(ASN1_RESTRICTED_TERMINAL k r) p w;
  match parse parse_asn1_identifier_U32 w with
  | Some (id, c1) ->
    let b1 = Seq.slice w c1 (Seq.length w) in
    (* The item parser is stated at nested refinement types that newer F*
       rejects when written explicitly, so use quantified equations instead *)
    parse_synth_eq_forall ();
    parse_filter_eq_forall ()
#pop-options
#pop-options
