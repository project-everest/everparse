module ASN1.Pulse.ParseChoice
#lang-pulse

(* Zero-copy parsing of CHOICE: the identifier read from the input selects
   the alternative, whose ILC is then parsed as a whole. *)

open Pulse.Lib.Pervasives
open LowParse.PulseParse.VReader
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module T = LowParse.Tot.Combinators
module SC = LowParse.Spec.Combinators
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC

let choice_k (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) : asn1_k (Set.as_set (List.Tot.map fst lc)) =
  ASN1_CHOICE_ILC lc pf

let choice_parse_eq (lp: list (asn1_id_t & gen_parser asn1_strong_parser_kind)) (b: SB.bytes)
: Lemma (SB.parse (make_gen_choice_strong_parser parse_asn1_identifier_U32 lp) b == (
    match SB.parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id, c1) ->
      begin match SB.parse (make_gen_choice_strong_payload_parser lp id) (Seq.slice b c1 (Seq.length b)) with
      | None -> None
      | Some (x, c2) -> Some ((x <: make_gen_choice_type (extract_types lp)), c1 + c2)
      end))
= T.parse_tagged_union_eq parse_asn1_identifier_U32 (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_strong_payload_parser lp) b

let parse_synth_eq_pat (#k: SB.parser_kind) (#t1 #t2: Type) (p: SB.parser k t1) (f: t1 -> Tot t2) (b: SB.bytes)
: Lemma
  (requires SC.synth_injective f)
  (ensures SB.parse (SC.parse_synth p f) b == SC.parse_synth' p f b)
  [SMTPat (SB.parse (SC.parse_synth p f) b)]
= SC.parse_synth_eq p f b

#push-options "--fuel 1 --ifuel 1"

let choice_payload_head_eq
  (id0: asn1_id_t) (gp: gen_parser asn1_strong_parser_kind)
  (tl: list (asn1_id_t & gen_parser asn1_strong_parser_kind))
  (b: SB.bytes)
: Lemma (match SB.parse (make_gen_choice_strong_payload_parser ((id0, gp) :: tl) id0) b with
    | None -> None? (SB.parse (Mkgenparser?.p gp) b)
    | Some (x, n) -> SB.parse (Mkgenparser?.p gp) b == Some (dsnd x, n))
= ()

let choice_payload_tail_eq
  (id0: asn1_id_t) (gp: gen_parser asn1_strong_parser_kind)
  (tl: list (asn1_id_t & gen_parser asn1_strong_parser_kind))
  (id: asn1_id_t { id <> id0 }) (b: SB.bytes)
: Lemma (SB.parse (make_gen_choice_strong_payload_parser ((id0, gp) :: tl) id) b == (
    match SB.parse (make_gen_choice_strong_payload_parser tl id) b with
    | None -> None
    | Some (y, n) -> Some (lemma_choice_cast (id0, Mkgenparser?.t gp) (extract_types tl) id y, n)))
= ()

#pop-options

let choice_cast_eq (#key: eqtype) (hd: key & Type) (tl: list (key & Type)) (id: key { id <> fst hd })
  (y: refine_with_tag (tag_of_gen_choice_type tl) id)
: Lemma (lemma_choice_cast hd tl id y == (| dfst y, dsnd y |))
= assert (lemma_choice_cast hd tl id y == (| dfst y, dsnd y |))
    by (FStar.Tactics.norm [delta_only [`%lemma_choice_cast]; zeta; iota]; FStar.Tactics.smt ())

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"

(* The identifier of a parsed CHOICE value is the one at the head of the input *)
let choice_retype (#key: eqtype) (l1 l2: list (key & Type)) (x: make_gen_choice_type l2)
: Lemma (requires l1 == l2)
  (ensures ((| dfst x, dsnd x |) <: make_gen_choice_type l1) == x)
= ()

let choice_id (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc)))
  (w: SB.bytes) (v: asn1_t (choice_k lc pf))
: Lemma
  (requires parsed #asn1_strong_parser_kind (asn1_as_parser (choice_k lc pf)) w v)
  (ensures (match SB.parse parse_asn1_identifier_U32 w with
    | Some (id, _) -> id == dfst v
    | None -> False))
= choice_parse_eq (asn1_lc_as_parser lc) w

let choice_head (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst ((id', c) :: tl))))
  (w: SB.bytes) (v: asn1_t (choice_k ((id', c) :: tl) pf))
: Lemma
  (requires parsed #asn1_strong_parser_kind (asn1_as_parser (choice_k ((id', c) :: tl) pf)) w v /\ dfst v == id')
  (ensures parsed #asn1_strong_parser_kind (asn1_as_parser (ASN1_ILC id' c)) w (dsnd v))
= let lp = asn1_lc_as_parser ((id', c) :: tl) in
  assert (lp == (id', Mkgenparser #asn1_strong_parser_kind (asn1_content_t c) (parse_asn1_LC (asn1_content_as_parser c))) :: asn1_lc_as_parser tl)
    by (FStar.Tactics.norm [delta_only [`%asn1_lc_as_parser; `%dasn1_lc_as_parser]; zeta; iota]; FStar.Tactics.smt ());
  choice_parse_eq lp w;
  ILC.ilc_eq id' (asn1_content_as_parser c) w;
  match SB.parse parse_asn1_identifier_U32 w with
  | Some (id, c1) ->
    if id = id' then choice_payload_head_eq (fst (List.Tot.hd lp)) (snd (List.Tot.hd lp)) (List.Tot.tl lp) (Seq.slice w c1 (Seq.length w))
  | None -> ()

let choice_tail (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst (hd :: tl))))
  (w: SB.bytes) (v: asn1_t (choice_k (hd :: tl) pf))
: Lemma
  (requires parsed #asn1_strong_parser_kind (asn1_as_parser (choice_k (hd :: tl) pf)) w v /\ dfst v <> fst hd)
  (ensures parsed #asn1_strong_parser_kind (asn1_as_parser (choice_k tl ())) w (| dfst v, dsnd v |))
= let lp = asn1_lc_as_parser (hd :: tl) in
  assert (lp == (fst hd, Mkgenparser #asn1_strong_parser_kind (asn1_content_t (snd hd)) (parse_asn1_LC (asn1_content_as_parser (snd hd)))) :: asn1_lc_as_parser tl)
    by (FStar.Tactics.norm [delta_only [`%asn1_lc_as_parser; `%dasn1_lc_as_parser]; zeta; iota]; FStar.Tactics.smt ());
  choice_parse_eq lp w;
  choice_parse_eq (asn1_lc_as_parser tl) w;
  match SB.parse parse_asn1_identifier_U32 w with
  | Some (id, c1) ->
    if id <> fst hd then begin
      let b1 = Seq.slice w c1 (Seq.length w) in
      choice_payload_tail_eq (fst (List.Tot.hd lp)) (snd (List.Tot.hd lp)) (List.Tot.tl lp) id b1;
      match SB.parse (make_gen_choice_strong_payload_parser (asn1_lc_as_parser tl) id) b1 with
      | Some (y, n2) ->
        choice_cast_eq (fst hd, asn1_content_t (snd hd)) (extract_types (asn1_lc_as_parser tl)) id y;
        choice_retype (asn1_lc_t tl) (extract_types (asn1_lc_as_parser tl)) y;
        choice_retype (asn1_lc_t (hd :: tl)) (extract_types lp) v
      | None -> ()
    end
  | None -> ()

#pop-options

(* Values of the head alternative / of the remaining alternatives *)

let choice_head_val (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst ((id', c) :: tl))))
  (v: make_gen_choice_type (asn1_lc_t ((id', c) :: tl))) (sq: squash (dfst v == id'))
: Tot (asn1_content_t c)
= dsnd v

let choice_tail_val (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst (hd :: tl))))
  (v: make_gen_choice_type (asn1_lc_t (hd :: tl))) (sq: squash (dfst v <> fst hd))
: Tot (make_gen_choice_type (asn1_lc_t tl))
= (| dfst v, dsnd v |)

(* Unfolding the relation *)

let lc_rel_single_eq (id': asn1_id_t) (#c: asn1_content_k) (#t: Type0) (cd: cdesc c t)
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst [(id', c)])))
  (pm: perm) (x: t)
  (v: make_gen_choice_type (asn1_lc_t [(id', c)])) (sq: squash (dfst v == id'))
: Lemma (lcrel true (LC_SINGLE id' cd) pm x v == crel true cd pm x (choice_head_val id' c [] pf v ()))
= assert_norm (lcrel true (LC_SINGLE id' cd) pm x v == (let (| id, v |) = v in if id = id' then crel true cd pm x v else pure False))

let lc_rel_cons_eq' (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: asn1_id_t & asn1_content_k) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pm: perm) (x: either t1 t2) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
: Lemma (lcrel true (LC_CONS id' cd dtl) pm x v == (
    let (| id, v |) = v in
    match x with
    | Inl a -> if id = id' then crel true cd pm a v else pure False
    | Inr b -> if id = id' then pure False else lcrel true dtl pm b (| id, v |)))
= assert_norm (lcrel true (LC_CONS id' cd dtl) pm x v == (
    let (| id, v |) = v in
    let x' : either t1 t2 = x in
    match x' with
    | Inl a -> if id = id' then crel true cd pm a v else pure False
    | Inr b -> if id = id' then pure False else lcrel true dtl pm b (| id, v |)))

let choice_head_step (id': asn1_id_t) (c: asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst ((id', c) :: tl))))
  (w: SB.bytes) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: tl))) (id: asn1_id_t)
: Lemma
  (requires parsed #asn1_strong_parser_kind (asn1_as_parser (choice_k ((id', c) :: tl) pf)) w v /\ dfst v == id /\ id == id')
  (ensures dfst v == id' /\ parsed #asn1_strong_parser_kind (asn1_as_parser (ASN1_ILC id' c)) w (choice_head_val id' c tl pf v ()))
= choice_head id' c tl pf w v

let choice_tail_step (hd: asn1_id_t & asn1_content_k) (tl: list (asn1_id_t & asn1_content_k))
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst (hd :: tl))))
  (w: SB.bytes) (v: make_gen_choice_type (asn1_lc_t (hd :: tl))) (id: asn1_id_t)
: Lemma
  (requires parsed #asn1_strong_parser_kind (asn1_as_parser (choice_k (hd :: tl) pf)) w v /\ dfst v == id /\ ~ (id == fst hd))
  (ensures dfst v <> fst hd /\ parsed #asn1_strong_parser_kind (asn1_as_parser (choice_k tl ())) w (choice_tail_val hd tl pf v ()) /\ dfst (choice_tail_val hd tl pf v ()) == id)
= choice_tail hd tl pf w v

let lc_rel_cons_head (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: asn1_id_t & asn1_content_k) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst ((id', c) :: hd2 :: tl2))))
  (pm: perm) (r: t1) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) (sq: squash (dfst v == id'))
: Lemma (lcrel true (LC_CONS id' cd dtl) pm (Inl #_ #t2 r) v == crel true cd pm r (choice_head_val id' c (hd2 :: tl2) pf v ()))
= lc_rel_cons_eq' id' cd dtl pm (Inl #_ #t2 r) v

let lc_rel_cons_tail (id': asn1_id_t) (#c: asn1_content_k) (#t1: Type0) (cd: cdesc c t1)
  (#hd2: asn1_id_t & asn1_content_k) (#tl2: list (asn1_id_t & asn1_content_k)) (#t2: Type0) (dtl: lcdesc (hd2 :: tl2) t2)
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst ((id', c) :: hd2 :: tl2))))
  (pm: perm) (r: t2) (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) (sq: squash (dfst v <> id'))
: Lemma (lcrel true (LC_CONS id' cd dtl) pm (Inr #t1 r) v == lcrel true dtl pm r (choice_tail_val (id', c) (hd2 :: tl2) pf v ()))
= let (| id, x |) = v in
  lc_rel_cons_eq' id' cd dtl pm (Inr #t1 r) (| id, x |);
  assert (choice_tail_val (id', c) (hd2 :: tl2) pf (| id, x |) () == (| id, x |))
    by (FStar.Tactics.norm [delta_only [`%choice_tail_val]; iota; zeta; primops]; FStar.Tactics.trefl ())

(* A parser for a CHOICE whose identifier has already been read *)

inline_for_extraction
let cparser (#lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (#t: Type0) (ld: lcdesc lc t) : Type =
  (id: asn1_id_t) ->
  (input: S.slice U8.t) ->
  (#pm: perm) ->
  (#w: Ghost.erased SB.bytes) ->
  (#v: Ghost.erased (make_gen_choice_type (asn1_lc_t lc))) ->
  stt t
    (S.pts_to input #pm w ** pure (parsed #asn1_strong_parser_kind (asn1_as_parser (choice_k lc pf)) w v /\ dfst (Ghost.reveal v) == id))
    (fun res -> lcrel true ld pm res v ** Trade.trade (lcrel true ld pm res v) (S.pts_to input #pm w))

inline_for_extraction
fn choice_nil (pf: squash (List.Tot.noRepeats (List.Tot.map fst ([] <: list (asn1_id_t & asn1_content_k)))))
: cparser pf LC_NIL
= (id: _) (input: _) (#pm: _) (#w: _) (#v: _)
{
  let x : squash False = ();
  unreachable ()
}

inline_for_extraction
fn choice_single
  (id': Ghost.erased asn1_id_t) (#c: Ghost.erased asn1_content_k) (#t: Type0) (cd: Ghost.erased (cdesc c t))
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst [(Ghost.reveal id', Ghost.reveal c)])))
  (phead: aparser #t #(asn1_t (ASN1_ILC id' c)) (crel true cd) #asn1_strong_parser_kind (asn1_as_parser (ASN1_ILC id' c)))
: cparser pf (LC_SINGLE (Ghost.reveal id') (Ghost.reveal cd))
= (id: _) (input: _) (#pm: _) (#w: _) (#v: _)
{
  choice_head id' c [] pf w v;
  let res = phead input #pm #w #(choice_head_val id' c [] pf v ());
  lc_rel_single_eq id' cd pf pm res v ();
  rewrite each (crel true cd pm res (choice_head_val id' c [] pf v ())) as (lcrel true (LC_SINGLE (Ghost.reveal id') (Ghost.reveal cd)) pm res v);
  res
}

inline_for_extraction
fn choice_cons
  (id': asn1_id_t) (#c: Ghost.erased asn1_content_k) (#t1: Type0) (cd: Ghost.erased (cdesc c t1))
  (#hd2: Ghost.erased (asn1_id_t & asn1_content_k)) (#tl2: Ghost.erased (list (asn1_id_t & asn1_content_k))) (#t2: Type0) (dtl: Ghost.erased (lcdesc (Ghost.reveal hd2 :: Ghost.reveal tl2) t2))
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst ((id', Ghost.reveal c) :: (Ghost.reveal hd2 :: Ghost.reveal tl2)))))
  (phead: aparser #t1 #(asn1_t (ASN1_ILC id' c)) (crel true cd) #asn1_strong_parser_kind (asn1_as_parser (ASN1_ILC id' c)))
  (ptail: cparser #(Ghost.reveal hd2 :: Ghost.reveal tl2) () dtl)
: cparser pf (LC_CONS id' (Ghost.reveal cd) (Ghost.reveal dtl))
= (id: _) (input: _) (#pm: _) (#w: _) (#v: _)
{
  if (ILC.asn1_id_eq id id') {
    choice_head_step id' c (Ghost.reveal hd2 :: Ghost.reveal tl2) pf w v id;
    let r = phead input #pm #w #(choice_head_val id' c (Ghost.reveal hd2 :: Ghost.reveal tl2) pf v ());
    let res : either t1 t2 = Inl #_ #t2 r;
    lc_rel_cons_head id' cd dtl pf pm r v ();
    rewrite each (crel true cd pm r (choice_head_val id' c (Ghost.reveal hd2 :: Ghost.reveal tl2) pf v ())) as (lcrel true (LC_CONS id' (Ghost.reveal cd) (Ghost.reveal dtl)) pm res v);
    res
  } else {
    choice_tail_step (id', Ghost.reveal c) (Ghost.reveal hd2 :: Ghost.reveal tl2) pf w v id;
    let r = ptail id input #pm #w #(choice_tail_val (id', Ghost.reveal c) (Ghost.reveal hd2 :: Ghost.reveal tl2) pf v ());
    let res : either t1 t2 = Inr #t1 r;
    lc_rel_cons_tail id' cd dtl pf pm r v ();
    rewrite each (lcrel true dtl pm r (choice_tail_val (id', Ghost.reveal c) (Ghost.reveal hd2 :: Ghost.reveal tl2) pf v ())) as (lcrel true (LC_CONS id' (Ghost.reveal cd) (Ghost.reveal dtl)) pm res v);
    res
  }
}

(* Reading the identifier, then dispatching *)

inline_for_extraction
fn choice_parser
  (lc: Ghost.erased (list (asn1_id_t & asn1_content_k)))
  (pf: squash (List.Tot.noRepeats (List.Tot.map fst (Ghost.reveal lc))))
  (#t: Type0) (ld: Ghost.erased (lcdesc lc t))
  (f: cparser pf ld)
: aparser #t #(asn1_t (choice_k lc pf)) (lcrel true ld) #asn1_strong_parser_kind (asn1_as_parser (choice_k lc pf))
= (input: _) (#pm: _) (#w: _) (#v: _)
{
  choice_id lc pf w v;
  let mut poff = 0sz;
  Seq.slice_length (Ghost.reveal w);
  let r = I.vread_identifier input poff;
  match r {
    Some id -> {
      f id input #pm #w #v
    }
    None -> {
      unreachable ()
    }
  }
}
