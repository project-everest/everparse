module ASN1.Pulse.ParseAdb.Lemmas

(* Value-level lemmas for the zero-copy ANY DEFINED BY parser:

   - the prefix machine (SEQUENCE items followed by a suffix) on validated
     bytes splits into a present item followed by the rest, or an absent
     item;
   - the suffix (key TLV, then payload) is laid out as an identifier, a
     length header, the key contents, then the payload;
   - the payload of a supported key is the SEQUENCE contents of the
     corresponding items; otherwise, if any, of the fallback items. *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.Any
open ASN1.Spec.Interpreter

module U32 = FStar.UInt32
module Seq = FStar.Seq
module SB = LowParse.Spec.Base
module SC = LowParse.Spec.Combinators
module SFL = LowParse.Spec.FLData
module SVG = LowParse.Spec.VLGen
module SDER = LowParse.Spec.DER
module T = LowParse.Tot.Combinators
module C = ASN1.Spec.Conformance
module TS = ASN1.Spec.ToValue.Sound
module ILC = ASN1.Pulse.ILC
module Sq = ASN1.Pulse.Sequence
module I = ASN1.Pulse.Interpreter
module P = ASN1.Pulse.Parse
module L = ASN1.Pulse.ParseSequence.Lemmas
module ADB = ASN1.Pulse.AnyDefinedBy

(* The prefix machine *)

let seqa_parsed (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: bytes) (v: asn1_sequence_any_t (List.Tot.map Mkgendcparser?.d its) t) : prop =
  P.parsed #asn1_weak_parser_kind (make_asn1_sequence_any_parser' its sfx None) w v

let sfx_shaped_at (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: bytes) : prop =
  match parse parse_asn1_identifier_U32 w with
  | None -> parse (Mkparsertwin?.p sfx) w == None
  | Some (id, c1) -> L.parsed_shift (L.res_nat (parse (Mkparsertwin?.p sfx) w)) (L.res_nat (parse (Mkparsertwin?.fp sfx id) (Seq.slice w c1 (Seq.length w)))) c1

let sfx_shaped (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) : prop =
  forall (w: bytes) . sfx_shaped_at sfx w

let sfx_shaped_elim (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: bytes)
: Lemma (requires sfx_shaped sfx) (ensures sfx_shaped_at sfx w)
= ()

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let seqa_none_some (its: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: bytes)
: Lemma
  (requires (Nil? its ==> sfx_shaped sfx))
  (ensures (match parse parse_asn1_identifier_U32 w with
    | None -> parse (make_asn1_sequence_any_parser' its sfx None) w == None
    | Some (id, c1) ->
      L.parsed_shift (L.res_nat (parse (make_asn1_sequence_any_parser' its sfx None) w)) (L.res_nat (parse (make_asn1_sequence_any_parser' its sfx (Some id)) (Seq.slice w c1 (Seq.length w)))) c1))
= L.identifier_nonempty w;
  match its with
  | [] ->
    TS.any'_veq_nil sfx None w;
    sfx_shaped_elim sfx w;
    begin match parse parse_asn1_identifier_U32 w with
    | None -> ()
    | Some (id, c1) -> TS.any'_veq_nil sfx (Some id) (Seq.slice w c1 (Seq.length w))
    end
  | _ ->
    TS.any'_veq_cons its sfx None w;
    let pb = make_asn1_sequence_any_parser'' its sfx in
    and_then_eq (C.any_guard_p None) pb w;
    match parse parse_asn1_identifier_U32 w with
    | None -> ()
    | Some (id, c1) ->
      let b1 = Seq.slice w c1 (Seq.length w) in
      TS.any'_veq_cons its sfx (Some id) b1;
      and_then_eq (C.any_guard_p (Some id)) pb b1;
      Seq.lemma_eq_elim b1 (Seq.slice b1 0 (Seq.length b1))
#pop-options

let seqa_cons_post (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: bytes)
  (v: asn1_sequence_any_t (List.Tot.map Mkgendcparser?.d (hd :: tl)) t) : prop
= let v' : asn1_decorated_t (Mkgendcparser?.d hd) & asn1_sequence_any_t (List.Tot.map Mkgendcparser?.d tl) t = v in
  let v1 = fst v' in
  let v2 = snd v' in
  match parse parse_asn1_identifier_U32 w with
  | None -> False
  | Some (id, _) ->
    if Set.mem id (Sq.item_set hd)
    then (match L.tlv_size w with
      | None -> False
      | Some n -> n <= Seq.length w /\ L.item_parsed hd (Seq.slice w 0 n) v1 /\ seqa_parsed tl sfx (Seq.slice w n (Seq.length w)) v2)
    else L.absent hd v1 /\ seqa_parsed tl sfx w v2

let any_body_veq (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (id: asn1_id_t) (b: bytes)
: Lemma (
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    let pb = make_asn1_sequence_any_parser_body (hd :: tl) (make_asn1_sequence_any_parser' tl sfx) id in
    if FStar.Set.mem id s
    then parse pb b == parse (parse_asn1_sequence_item_twin hd id `nondep_then` make_asn1_sequence_any_parser' tl sfx None) b
    else match de with
    | PLAIN -> True
    | _ -> (match generate_defaultable_item hd with
      | Some defv -> parse pb b == parse (weaken asn1_strong_parser_kind (parse_ret defv) `nondep_then` make_asn1_sequence_any_parser' tl sfx (Some id)) b
      | None -> True))
= match tl with
  | [] -> TS.any_body_veq_single hd sfx id b
  | hd' :: tl' -> TS.any_body_veq_cons hd hd' tl' sfx id b

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let seqa_cons (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: bytes)
  (v: asn1_sequence_any_t (List.Tot.map Mkgendcparser?.d (hd :: tl)) t)
: Lemma
  (requires (seqa_parsed (hd :: tl) sfx w v /\ L.item_shaped hd /\ (Nil? tl ==> sfx_shaped sfx)))
  (ensures (seqa_cons_post hd tl sfx w v))
= let its = hd :: tl in
  L.identifier_nonempty w;
  TS.any'_veq_cons its sfx None w;
  let pb = make_asn1_sequence_any_parser'' its sfx in
  and_then_eq (C.any_guard_p None) pb w;
  match parse parse_asn1_identifier_U32 w with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice w c1 (Seq.length w) in
    TS.any''_veq hd tl sfx id b1;
    any_body_veq hd tl sfx id b1;
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    if Set.mem id s
    then begin
      let p1 = parse_asn1_sequence_item_twin hd id in
      let p2 = make_asn1_sequence_any_parser' tl sfx None in
      nondep_then_eq p1 p2 b1;
      let Some (x1, n2) = parse p1 b1 in
      assert (L.lc_shaped p1);
      assert (Sq.consumed #asn1_strong_parser_kind p1 b1 == Some n2);
      assert (L.tlv_size w == Some (c1 + n2));
      let w' = Seq.slice w 0 (c1 + n2) in
      L.slice_prefix_slice w c1 n2;
      parse_strong_prefix #asn1_strong_parser_kind parse_asn1_identifier_U32 w w';
      parse_strong_prefix #asn1_strong_parser_kind p1 b1 (Seq.slice b1 0 n2);
      Seq.slice_slice w c1 (Seq.length w) n2 (Seq.length b1)
    end
    else match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_any_parser' tl sfx (Some id) in
      nondep_then_eq p1 p2 b1;
      Seq.lemma_eq_elim b1 (Seq.slice b1 0 (Seq.length b1));
      seqa_none_some tl sfx w
#pop-options

let seqa_nil (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (w: bytes) (v: t)
: Lemma
  (requires (seqa_parsed [] sfx w v))
  (ensures (P.parsed #asn1_weak_parser_kind (Mkparsertwin?.p sfx) w v))
= TS.any'_veq_nil sfx None w

(* The suffix: key TLV, then payload *)

let ptu (kid: asn1_id_t) (key_k: asn1_terminal_k) (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
: Tot (parser (and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) data_t)
= T.parse_tagged_union (ADB.key_p kid key_k) tag pl

let ptu_twin (kid: asn1_id_t) (key_k: asn1_terminal_k) (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (id: asn1_id_t)
: Tot (parser (and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) data_t)
= T.parse_tagged_union (ADB.key_fp kid key_k id) tag pl

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let ptu_shaped (kid: asn1_id_t) (key_k: asn1_terminal_k) (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (w: bytes)
: Lemma (match parse parse_asn1_identifier_U32 w with
    | None -> parse (ptu kid key_k tag pl) w == None
    | Some (id, c1) -> L.parsed_shift (L.res_nat (parse (ptu kid key_k tag pl) w)) (L.res_nat (parse (ptu_twin kid key_k tag pl id) (Seq.slice w c1 (Seq.length w)))) c1)
= let p = asn1_terminal_as_parser key_k in
  T.parse_tagged_union_eq (ADB.key_p kid key_k) tag pl w;
  ILC.ilc_eq kid #(ASN1_TERMINAL key_k) p w;
  match parse parse_asn1_identifier_U32 w with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice w c1 (Seq.length w) in
    T.parse_tagged_union_eq (ADB.key_fp kid key_k id) tag pl b1;
    if id = kid
    then begin
      match parse (parse_asn1_LC #(ASN1_TERMINAL key_k) p) b1 with
      | None -> ()
      | Some (_, c2) ->
        Seq.slice_slice w c1 (Seq.length w) c2 (Seq.length b1)
    end
#pop-options

let sfx_none_shaped (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk))
: Lemma (sfx_shaped (ADB.adb_sfx_none kid key_k ls))
= let lp = asn1_ls_as_parser (asn1_terminal_t key_k) ls in
  let aux (w: bytes) : Lemma (sfx_shaped_at (ADB.adb_sfx_none kid key_k ls) w) =
    ptu_shaped kid key_k (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp) w
  in
  Classical.forall_intro aux

let sfx_some_shaped (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
: Lemma (sfx_shaped (ADB.adb_sfx_some kid key_k ls fb))
= let lp = asn1_ls_as_parser (asn1_terminal_t key_k) ls in
  let aux (w: bytes) : Lemma (sfx_shaped_at (ADB.adb_sfx_some kid key_k ls fb) w) =
    ptu_shaped kid key_k (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (ADB.adb_fb fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (ADB.adb_fb fb)) w
  in
  Classical.forall_intro aux

(* The layout of a parsed suffix *)

let sfx_layout_post (key_k: asn1_terminal_k) (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (w: bytes) (v: data_t) : prop
= match parse parse_asn1_identifier_U32 w with
  | None -> False
  | Some (_, c1) ->
    match parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w c1 (Seq.length w)) with
    | None -> False
    | Some (len, c2) ->
      let n = c1 + c2 + U32.v len in
      n <= Seq.length w /\
      P.parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (Seq.slice w (c1 + c2) n) (tag v) /\
      (match parse (pl (tag v)) (Seq.slice w n (Seq.length w)) with
       | Some (v', c3) -> (v' <: data_t) == v /\ c3 == Seq.length w - n
       | None -> False)

#push-options "--z3rlimit 128 --fuel 1 --ifuel 2"
let sfx_layout (kid: asn1_id_t) (key_k: asn1_terminal_k) (#data_t: Type)
  (tag: data_t -> Tot (asn1_terminal_t key_k))
  (pl: (x: asn1_terminal_t key_k) -> Tot (asn1_weak_parser (refine_with_tag tag x)))
  (w: bytes) (v: data_t)
: Lemma
  (requires (P.parsed #(and_then_kind asn1_strong_parser_kind asn1_weak_parser_kind) (ptu kid key_k tag pl) w v))
  (ensures (sfx_layout_post key_k tag pl w v))
= let p = asn1_terminal_as_parser key_k in
  T.parse_tagged_union_eq (ADB.key_p kid key_k) tag pl w;
  ILC.ilc_eq kid #(ASN1_TERMINAL key_k) p w;
  match parse parse_asn1_identifier_U32 w with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice w c1 (Seq.length w) in
    ILC.lc_eq p b1;
    SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) #asn1_weak_parser_kind #(asn1_terminal_t key_k) p b1;
    match parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) b1 with
    | None -> ()
    | Some (len, c2) ->
      let l = U32.v len in
      let b2 = Seq.slice b1 c2 (Seq.length b1) in
      if Seq.length b2 < l then ()
      else begin
        Seq.slice_slice w c1 (Seq.length w) c2 (Seq.length b1);
        Seq.slice_slice w (c1 + c2) (Seq.length w) 0 l;
        Seq.slice_slice w c1 (Seq.length w) (c2 + l) (Seq.length b1)
      end
#pop-options

(* The payload, selected by the key *)

let ady (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk)) : Type =
  make_gen_choice_type (asn1_any_t_core (asn1_terminal_t key_k) ls)

let lp_of (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk)) =
  asn1_ls_as_parser (asn1_terminal_t key_k) ls

let pl_parsed (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (wp: bytes) (v: ady key_k ls) : prop =
  match parse (make_gen_choice_weak_payload_parser (lp_of key_k ls) (dfst v)) wp with
  | Some (v', n) -> (v' <: ady key_k ls) == v /\ n == Seq.length wp
  | None -> False

let ady_head_val (#key_k: asn1_terminal_k) (x: asn1_terminal_t key_k) (y: asn1_gen_items_lk) (tl: list (asn1_terminal_t key_k & asn1_gen_items_lk))
  (v: ady key_k ((x, y) :: tl)) (sq: squash (dfst v == x))
: Tot (asn1_sequence_t_core (dsnd y))
= dsnd v

let ady_tail_val (#key_k: asn1_terminal_k) (x: asn1_terminal_t key_k) (y: asn1_gen_items_lk) (tl: list (asn1_terminal_t key_k & asn1_gen_items_lk))
  (v: ady key_k ((x, y) :: tl)) (sq: squash (dfst v <> x))
: Tot (ady key_k tl)
= (| dfst v, dsnd v |)

let pl_nil (key_k: asn1_terminal_k) (wp: bytes) (v: ady key_k [])
: Lemma (requires pl_parsed key_k [] wp v) (ensures False)
= ()

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let pl_head (#key_k: asn1_terminal_k) (x: asn1_terminal_t key_k) (y: asn1_gen_items_lk) (tl: list (asn1_terminal_t key_k & asn1_gen_items_lk))
  (wp: bytes) (v: ady key_k ((x, y) :: tl))
: Lemma
  (requires pl_parsed key_k ((x, y) :: tl) wp v /\ dfst v == x)
  (ensures P.parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE y)) wp (ady_head_val x y tl v ()))
= let t = asn1_terminal_t key_k in
  let lp = asn1_ls_as_parser t ((x, y) :: tl) in
  let p = make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd y)) in
  TS.ls_as_parser_cons t x y tl;
  parse_synth_eq p (attach_tag lp x) wp

let pl_tail (#key_k: asn1_terminal_k) (x: asn1_terminal_t key_k) (y: asn1_gen_items_lk) (tl: list (asn1_terminal_t key_k & asn1_gen_items_lk))
  (wp: bytes) (v: ady key_k ((x, y) :: tl))
: Lemma
  (requires pl_parsed key_k ((x, y) :: tl) wp v /\ dfst v <> x)
  (ensures pl_parsed key_k tl wp (ady_tail_val x y tl v ()))
= let t = asn1_terminal_t key_k in
  let hdp = TS.ls_hd x y in
  let key = dfst v in
  TS.ls_as_parser_cons t x y tl;
  TS.weak_payload_unfold hdp (asn1_ls_as_parser t tl) key wp;
  match parse (make_gen_choice_weak_payload_parser (asn1_ls_as_parser t tl) key) wp with
  | Some (v', _) ->
    let (| i, z |) = v' in
    assert (lemma_choice_cast (fst hdp, Mkgenparser?.t (snd hdp)) (extract_types (asn1_ls_as_parser t tl)) key (| i, z |) == (| i, z |)) by (FStar.Tactics.norm [delta_only [`%lemma_choice_cast]; zeta; iota]; FStar.Tactics.smt ())
  | None -> ()
#pop-options

(* The payload, with a fallback *)

let ady_fb (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) : Type =
  make_gen_choice_type_with_fallback (asn1_any_t_core (asn1_terminal_t key_k) ls) (asn1_sequence_t_core (dsnd fb))

let pl_fb_parsed (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (wp: bytes) (v: ady_fb key_k ls fb) : prop =
  match parse (make_gen_choice_with_fallback_weak_payload_parser (lp_of key_k ls) (ADB.adb_fb fb) (dfst v)) wp with
  | Some (v', n) -> (v' <: ady_fb key_k ls fb) == v /\ n == Seq.length wp
  | None -> False

let ady_fb_nil_val (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (v: ady_fb key_k [] fb)
: Tot (asn1_sequence_t_core (dsnd fb))
= dsnd v

let ady_fb_head_val (#key_k: asn1_terminal_k) (x: asn1_terminal_t key_k) (y: asn1_gen_items_lk) (tl: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (v: ady_fb key_k ((x, y) :: tl) fb) (sq: squash (dfst v == x))
: Tot (asn1_sequence_t_core (dsnd y))
= dsnd v

let ady_fb_tail_val (#key_k: asn1_terminal_k) (x: asn1_terminal_t key_k) (y: asn1_gen_items_lk) (tl: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (v: ady_fb key_k ((x, y) :: tl) fb) (sq: squash (dfst v <> x))
: Tot (ady_fb key_k tl fb)
= (| dfst v, dsnd v |)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 1"
let pl_fb_nil (#key_k: asn1_terminal_k) (fb: asn1_gen_items_lk) (wp: bytes) (v: ady_fb key_k [] fb)
: Lemma
  (requires pl_fb_parsed key_k [] fb wp v)
  (ensures P.parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE fb)) wp (ady_fb_nil_val fb v))
= let t = asn1_terminal_t key_k in
  let lp = asn1_ls_as_parser t [] in
  let p = make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd fb)) in
  parse_synth_eq p (attach_tag_with_fallback lp (ADB.adb_fb fb) (dfst v)) wp

let pl_fb_head (#key_k: asn1_terminal_k) (x: asn1_terminal_t key_k) (y: asn1_gen_items_lk) (tl: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (wp: bytes) (v: ady_fb key_k ((x, y) :: tl) fb)
: Lemma
  (requires pl_fb_parsed key_k ((x, y) :: tl) fb wp v /\ dfst v == x)
  (ensures P.parsed #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE y)) wp (ady_fb_head_val x y tl fb v ()))
= let t = asn1_terminal_t key_k in
  let lp = asn1_ls_as_parser t ((x, y) :: tl) in
  let p = make_asn1_sequence_parser (asn1_sequence_as_parser (dsnd y)) in
  TS.ls_as_parser_cons t x y tl;
  parse_synth_eq p (attach_tag_with_fallback lp (ADB.adb_fb fb) x) wp

let pl_fb_tail (#key_k: asn1_terminal_k) (x: asn1_terminal_t key_k) (y: asn1_gen_items_lk) (tl: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (wp: bytes) (v: ady_fb key_k ((x, y) :: tl) fb)
: Lemma
  (requires pl_fb_parsed key_k ((x, y) :: tl) fb wp v /\ dfst v <> x)
  (ensures pl_fb_parsed key_k tl fb wp (ady_fb_tail_val x y tl fb v ()))
= let t = asn1_terminal_t key_k in
  let hdp = TS.ls_hd x y in
  let key = dfst v in
  let gfb = ADB.adb_fb fb in
  TS.ls_as_parser_cons t x y tl;
  TS.weak_payload_fb_unfold hdp (asn1_ls_as_parser t tl) gfb key wp;
  match parse (make_gen_choice_with_fallback_weak_payload_parser (asn1_ls_as_parser t tl) gfb key) wp with
  | Some (v', _) ->
    let (| i, z |) = v' in
    assert (lemma_choice_with_fallback_cast (fst hdp, Mkgenparser?.t (snd hdp)) (extract_types (asn1_ls_as_parser t tl)) (Mkgenparser?.t gfb) key (| i, z |) == (| i, z |)) by (FStar.Tactics.norm [delta_only [`%lemma_choice_with_fallback_cast]; zeta; iota]; FStar.Tactics.smt ())
  | None -> ()
#pop-options

(* The suffix layout, with the payload predicates *)

let layout_post (key_k: asn1_terminal_k) (key: asn1_terminal_t key_k) (q: bytes -> prop) (w: bytes) : prop =
  match parse parse_asn1_identifier_U32 w with
  | None -> False
  | Some (_, c1) ->
    match parse (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice w c1 (Seq.length w)) with
    | None -> False
    | Some (len, c2) ->
      let n = c1 + c2 + U32.v len in
      n <= Seq.length w /\
      P.parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (Seq.slice w (c1 + c2) n) key /\
      q (Seq.slice w n (Seq.length w))

let sfx_none_layout (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (w: bytes) (v: ady key_k ls)
: Lemma
  (requires P.parsed #asn1_weak_parser_kind (Mkparsertwin?.p (ADB.adb_sfx_none kid key_k ls)) w v)
  (ensures layout_post key_k (dfst v) (fun wp -> pl_parsed key_k ls wp v) w)
= let lp = lp_of key_k ls in
  sfx_layout kid key_k (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp) w v

let sfx_some_layout (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_terminal_t key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (w: bytes) (v: ady_fb key_k ls fb)
: Lemma
  (requires P.parsed #asn1_weak_parser_kind (Mkparsertwin?.p (ADB.adb_sfx_some kid key_k ls fb)) w v)
  (ensures layout_post key_k (dfst v) (fun wp -> pl_fb_parsed key_k ls fb wp v) w)
= let lp = lp_of key_k ls in
  sfx_layout kid key_k (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (ADB.adb_fb fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (ADB.adb_fb fb)) w v

(* Comparing the key *)

let key_check (key_k: asn1_terminal_k) (x key: asn1_terminal_t key_k) (wk: bytes)
: Lemma
  (requires P.parsed #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) wk key)
  (ensures (Some? (SB.parse (SC.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (ADB.key_eq x)) (Seq.slice wk 0 (Seq.length wk))) <==> key = x))
= Seq.lemma_eq_elim wk (Seq.slice wk 0 (Seq.length wk));
  SC.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser key_k) (ADB.key_eq x) wk
