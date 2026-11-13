module ASN1.Pulse.JitAdbSeq
#lang-pulse
(* Exactness of the JIT writers of the prefix items of ANY DEFINED BY
   (ASN1.Pulse.JitWriter), as for SEQUENCE components
   (ASN1.Pulse.JitWriter.SeqLemmas): from the well-formedness of the tags
   of the prefix items (`asn1_any_prefix_k_wf`) instead of runtime checks
   on identifiers. The raw bytes of the suffix start with the identifier
   of the key. *)
open Pulse.Lib.Pervasives
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Choice
open ASN1.Spec.Any
open ASN1.Spec.Sequence
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.RawRel

module SB = LowParse.Spec.Base
module FS = FStar.Set
module Sq = ASN1.Pulse.Sequence
module SA = ASN1.Pulse.SeqAny
module ADB = ASN1.Pulse.AnyDefinedBy
module In = ASN1.Pulse.Interpreter
module IE = ASN1.Spec.IdentifierU32.Enc
module L = ASN1.Pulse.JitWriter.Lemmas
module SL = ASN1.Pulse.JitWriter.SeqLemmas
module PSL = ASN1.Pulse.ParseSequence.Lemmas
module JA = ASN1.Pulse.JitAdb
module JK = ASN1.Pulse.JitAdbKey
module JF = ASN1.Pulse.JitFrame
module WA = ASN1.Pulse.WriteAdb

(* Acceptance of the prefix items, then the suffix *)

let aacc_ne (items: list gen_decorated_parser_twin) (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t) (b: SB.bytes)
: Lemma
  (requires (JA.twin_ok sfx /\ L.acc #asn1_weak_parser_kind (SA.seqa_p items sfx None) b))
  (ensures (JA.aacc items sfx b))
= JA.seqa_none items sfx b;
  L.ident_empty ();
  if Seq.length b = 0 then assert (Seq.equal b Seq.empty)

let slice_app (a b: SB.bytes)
: Lemma (Seq.slice (a `Seq.append` b) (Seq.length a) (Seq.length a + Seq.length b) == b)
= assert (Seq.equal (Seq.slice (a `Seq.append` b) (Seq.length a) (Seq.length a + Seq.length b)) b)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 128"
let aacc_cons_inv' (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin)
  (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t)
  (id: asn1_id_t) (c x2: SB.bytes)
: Lemma
  (requires (JA.twin_ok sfx /\ FS.mem id (Sq.item_set hd) /\ PSL.item_shaped hd /\ JA.aacc (hd :: tl) sfx (enc_tlv id true c `Seq.append` x2)))
  (ensures (L.iacc [hd] (enc_tlv id true c) /\ JA.aacc tl sfx x2))
= let hdr = enc_hdr true (Seq.length c) in
  let r1 = hdr `Seq.append` c in
  let x1 = enc_tlv id true c in
  let x = x1 `Seq.append` x2 in
  let ie = IE.asn1_id_enc id in
  let rr = r1 `Seq.append` x2 in
  Seq.append_assoc ie r1 x2;
  IE.parse_asn1_identifier_U32_enc id rr;
  IE.parse_asn1_identifier_U32_enc id r1;
  L.enc_tlv_ne id c;
  SA.seqa_cons_eq (hd :: tl) sfx None x;
  Sq.seq_cons_none [hd] x1;
  let c1 = Seq.length ie in
  slice_app ie rr;
  slice_app ie r1;
  SA.seqa_body_eq hd tl sfx id rr;
  Sq.seq_single_some hd id r1;
  let tw = parse_asn1_sequence_item_twin hd id in
  assert (PSL.lc_shaped tw);
  L.lc_size_tlv c x2;
  match Sq.consumed #asn1_strong_parser_kind tw rr with
  | None -> ()
  | Some n1 ->
    assert (Seq.equal (Seq.slice rr 0 (Seq.length r1)) r1);
    L.strong_prefix_down tw r1 rr n1;
    assert (Seq.equal (Seq.slice rr n1 (Seq.length rr)) x2);
    aacc_ne tl sfx x2
#pop-options

let aacc_cons_inv (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin)
  (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t)
  (x1 x2: SB.bytes)
: Lemma
  (requires (JA.twin_ok sfx /\ L.framed (Sq.item_set hd) x1 /\ PSL.item_shaped hd /\ JA.aacc (hd :: tl) sfx (x1 `Seq.append` x2)))
  (ensures (L.iacc [hd] x1 /\ JA.aacc tl sfx x2))
= eliminate exists (id: asn1_id_t) (c: SB.bytes) . FS.mem id (Sq.item_set hd) /\ x1 == enc_tlv id true c
  with aacc_cons_inv' hd tl sfx id c x2

#push-options "--fuel 1 --ifuel 1 --z3rlimit 64"
let aacc_absent_head (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin)
  (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t)
  (x2: SB.bytes)
: Lemma
  (requires (JA.twin_ok sfx /\ ~ (PLAIN? (Sq.item_dec hd)) /\ SL.avoids (Sq.item_set hd) x2))
  (ensures (JA.aacc (hd :: tl) sfx x2 <==> JA.aacc tl sfx x2))
= L.ident_empty ();
  SA.seqa_cons_eq (hd :: tl) sfx None x2;
  JA.seqa_none tl sfx x2;
  if Seq.length x2 = 0
  then ()
  else match SB.parse parse_asn1_identifier_U32 x2 with
  | None -> ()
  | Some (id, c1) -> SA.seqa_body_eq hd tl sfx id (Seq.slice x2 c1 (Seq.length x2))
#pop-options

let aacc_cons_inv_wf (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin)
  (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t)
  (x1 x2: SB.bytes)
: Lemma
  (requires (JA.twin_ok sfx /\ SL.dfe hd x1 /\ SL.avoids (SL.hs hd) x2 /\ PSL.item_shaped hd /\ JA.aacc (hd :: tl) sfx (x1 `Seq.append` x2)))
  (ensures (L.iacc [hd] x1 /\ JA.aacc tl sfx x2))
= if Seq.length x1 = 0
  then begin
    Seq.lemma_empty x1;
    Classical.move_requires (L.framed_ne (Sq.item_set hd)) x1;
    assert (~ (PLAIN? (Sq.item_dec hd)) /\ SL.avoids (Sq.item_set hd) x2);
    Seq.append_empty_l x2;
    L.iacc_single_empty hd;
    aacc_absent_head hd tl sfx x2
  end
  else begin
    assert (L.framed (Sq.item_set hd) x1);
    aacc_cons_inv hd tl sfx x1 x2
  end

let slice_pre (v: SB.bytes) (a b: nat)
: Lemma (requires (a <= b /\ b <= Seq.length v))
  (ensures (Seq.slice (Seq.slice v a (Seq.length v)) 0 (b - a) == Seq.slice v a b))
= assert (Seq.equal (Seq.slice (Seq.slice v a (Seq.length v)) 0 (b - a)) (Seq.slice v a b))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 64"
let aacc_cons_wf (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin)
  (#t: Type) (sfx: parser_twin asn1_weak_parser_kind t)
  (v: SB.bytes) (p2: nat) (p1: nat { p2 <= p1 }) (p0: nat { p1 <= p0 /\ p0 <= Seq.length v })
: Lemma
  (requires (JA.twin_ok sfx /\
    SL.dfe hd (Seq.slice v p2 p1) /\ SL.avoids (SL.hs hd) (Seq.slice v p1 p0) /\
    L.iacc [hd] (Seq.slice v p2 p1) /\ JA.aacc tl sfx (Seq.slice v p1 p0)))
  (ensures (JA.aacc (hd :: tl) sfx (Seq.slice v p2 p0)))
= let xh = Seq.slice v p2 p1 in
  let xt = Seq.slice v p1 p0 in
  if p2 < p1
  then begin
    L.framed_pid (Sq.item_set hd) xh;
    let vr = Seq.slice v p2 (Seq.length v) in
    slice_pre v p2 p1;
    L.ident_prefix xh vr
  end
  else if p1 < p0
  then begin
    Classical.move_requires (L.framed_ne (Sq.item_set hd)) xh;
    L.ident_empty ();
    JA.seqa_none tl sfx xt;
    let vr = Seq.slice v p1 (Seq.length v) in
    slice_pre v p1 p0;
    L.ident_prefix xt vr
  end;
  JA.aacc_cons hd tl sfx v p2 p1 p0
#pop-options

(* The same, abstracted over the suffix *)

let acons_inv_at (aa: list gen_decorated_parser_twin -> SB.bytes -> prop) (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (x1 x2: SB.bytes) : prop =
  (SL.dfe hd x1 /\ SL.avoids (SL.hs hd) x2 /\ PSL.item_shaped hd /\ aa (hd :: tl) (x1 `Seq.append` x2)) ==>
  (L.iacc [hd] x1 /\ aa tl x2)

let acons_wf_at (aa: list gen_decorated_parser_twin -> SB.bytes -> prop) (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (v: SB.bytes) (p2 p1 p0: nat) : prop =
  (p2 <= p1 /\ p1 <= p0 /\ p0 <= Seq.length v /\
    SL.dfe hd (Seq.slice v p2 p1) /\ SL.avoids (SL.hs hd) (Seq.slice v p1 p0) /\
    L.iacc [hd] (Seq.slice v p2 p1) /\ aa tl (Seq.slice v p1 p0)) ==>
  aa (hd :: tl) (Seq.slice v p2 p0)

let acons_x_ok (aa: list gen_decorated_parser_twin -> SB.bytes -> prop) : prop =
  (forall hd tl x1 x2 . {:pattern (acons_inv_at aa hd tl x1 x2)} acons_inv_at aa hd tl x1 x2) /\
  (forall hd tl v p2 p1 p0 . {:pattern (acons_wf_at aa hd tl v p2 p1 p0)} acons_wf_at aa hd tl v p2 p1 p0)

let aacc_acons_x (#st: Type) (sfx: parser_twin asn1_weak_parser_kind st) (aa: list gen_decorated_parser_twin -> SB.bytes -> prop)
  (heq: (items: list gen_decorated_parser_twin) -> (w: SB.bytes) -> Lemma (aa items w <==> JA.aacc items sfx w))
: Lemma (requires (JA.twin_ok sfx)) (ensures (acons_x_ok aa))
= let aux1 (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (x1 x2: SB.bytes)
  : Lemma (acons_inv_at aa hd tl x1 x2)
  = heq (hd :: tl) (x1 `Seq.append` x2);
    heq tl x2;
    Classical.move_requires (aacc_cons_inv_wf hd tl sfx x1) x2
  in
  let aux2 (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (v: SB.bytes) (p2 p1 p0: nat)
  : Lemma (acons_wf_at aa hd tl v p2 p1 p0)
  = if p2 <= p1 && p1 <= p0 && p0 <= Seq.length v
    then begin
      heq tl (Seq.slice v p1 p0);
      heq (hd :: tl) (Seq.slice v p2 p0);
      Classical.move_requires (aacc_cons_wf hd tl sfx v p2 p1) p0
    end
  in
  introduce forall hd tl x1 x2 . acons_inv_at aa hd tl x1 x2
  with aux1 hd tl x1 x2;
  introduce forall hd tl v p2 p1 p0 . acons_wf_at aa hd tl v p2 p1 p0
  with aux2 hd tl v p2 p1 p0

(* Converses of `JA.acc_content_*` and `JA.aacc_nil_*` *)

let acc_content_none_inv
  (ipd: id_decs) (prefix: asn1_gen_items_l ipd)
  (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (pf: squash (asn1_any_prefix_k_wf (FS.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (w: SB.bytes)
: Lemma (requires (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls None pf pf')) w))
  (ensures (JA.aacc (In.twins_of prefix) (ADB.adb_sfx_none kid key_k ls) w))
= ADB.adb_prefix_content_none ipd prefix kid key_k ls pf pf' w;
  JA.twin_ok_none kid key_k ls;
  aacc_ne (In.twins_of prefix) (ADB.adb_sfx_none kid key_k ls) w

let acc_content_some_inv
  (ipd: id_decs) (prefix: asn1_gen_items_l ipd)
  (kid: asn1_id_t) (key_k: asn1_terminal_k)
  (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (fb: asn1_gen_items_lk)
  (pf: squash (asn1_any_prefix_k_wf (FS.singleton kid) ipd))
  (pf': squash (List.Tot.noRepeats (List.Tot.map fst ls)))
  (w: SB.bytes)
: Lemma (requires (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_ANY_DEFINED_BY ipd prefix kid key_k ls (Some fb) pf pf')) w))
  (ensures (JA.aacc (In.twins_of prefix) (ADB.adb_sfx_some kid key_k ls fb) w))
= ADB.adb_prefix_content_some ipd prefix kid key_k ls fb pf pf' w;
  JA.twin_ok_some kid key_k ls fb;
  aacc_ne (In.twins_of prefix) (ADB.adb_sfx_some kid key_k ls fb) w

#push-options "--z3rlimit 32"
let aacc_nil_none_inv (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (w: SB.bytes)
: Lemma (requires (JA.aacc [] (ADB.adb_sfx_none kid key_k ls) w)) (ensures (JA.adbacc kid key_k ls w))
= let lp = JA.lp key_k ls in
  SA.seqa_nil_eq (ADB.adb_sfx_none kid key_k ls) None w;
  ADB.adb_sfx_none_eq kid key_k ls None w;
  JA.kd_tu kid key_k (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_weak_payload_parser lp) w

let aacc_nil_some_inv (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (w: SB.bytes)
: Lemma (requires (JA.aacc [] (ADB.adb_sfx_some kid key_k ls fb) w)) (ensures (JA.afbacc kid key_k ls fb w))
= let lp = JA.lp key_k ls in
  SA.seqa_nil_eq (ADB.adb_sfx_some kid key_k ls fb) None w;
  ADB.adb_sfx_some_eq kid key_k ls fb None w;
  JA.kd_tu kid key_k (tag_of_gen_choice_type_with_fallback (extract_types lp) (Mkgenparser?.t (ADB.adb_fb fb))) (make_gen_choice_with_fallback_weak_payload_parser lp (ADB.adb_fb fb)) w
#pop-options

(* Well-formedness of the tags of the prefix items, after the head *)

let rec any_wf'_sub (ks: FS.set asn1_id_t) (l: id_decs) (s1 s2: FS.set asn1_id_t)
: Lemma (requires (asn1_any_prefix_k_wf' ks l s2 /\ FS.subset s1 s2)) (ensures (asn1_any_prefix_k_wf' ks l s1))
  (decreases l)
= match l with
  | [] -> ()
  | (s', d) :: tl ->
    if PLAIN? d then () else any_wf'_sub ks tl (FS.union s1 s') (FS.union s2 s')

let any_wf'_wf (ks: FS.set asn1_id_t) (l: id_decs) (s: FS.set asn1_id_t)
: Lemma (requires (asn1_any_prefix_k_wf' ks l s)) (ensures (asn1_any_prefix_k_wf ks l))
= match l with
  | [] -> ()
  | (s', d) :: tl ->
    if PLAIN? d then () else any_wf'_sub ks tl s' (FS.union s s')

let any_wf_tl (ks: FS.set asn1_id_t) (hd: FS.set asn1_id_t & asn1_decorator) (tl: id_decs)
: Lemma (requires (asn1_any_prefix_k_wf ks (hd :: tl))) (ensures (asn1_any_prefix_k_wf ks tl))
= let (s', d) = hd in
  if PLAIN? d then () else any_wf'_wf ks tl s'

(* The raw bytes of the suffix start with the identifier of the key *)

let key_framed (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k)
: Lemma (L.framed (FS.singleton kid) (WA.raw_key_enc kid key_k kx))
= JK.raw_key_enc_c kid key_k kx;
  L.framed_intro kid (FS.singleton kid) (JK.raw_key_c key_k kx)

ghost
fn av_false (t: Type0) (s: FS.set asn1_id_t) (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires raw_false t pm y x
ensures raw_false t pm y x ** pure (SL.avoids s x)
{
  unfold (raw_false t pm y x);
  unreachable ()
}

ghost
fn av_pre_framed (e: SB.bytes) (#t: Type0) (r: bprel t) (s s': FS.set asn1_id_t) (sq: squash (FS.disjoint s s' /\ L.framed s' e))
  (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires raw_pre e r pm y x
ensures raw_pre e r pm y x ** pure (SL.avoids s x)
{
  unfold (raw_pre e r pm y x);
  with w' . assert (r pm y w');
  SL.avoids_framed s s' e w';
  fold (raw_pre e r pm y x);
}

ghost
fn av_cat_fr (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (s s': FS.set asn1_id_t) (sq: squash (FS.disjoint s s')) (f: JF.fr_t r1 s')
  (pm: perm) (y: t1 & t2) (x: Ghost.erased SB.bytes)
requires raw_cat r1 r2 pm y x
ensures raw_cat r1 r2 pm y x ** pure (SL.avoids s x)
{
  unfold (raw_cat r1 r2 pm y x);
  with w1 w2 . assert (r1 pm (fst y) w1 ** r2 pm (snd y) w2);
  f pm (fst y) w1;
  SL.avoids_framed s s' w1 w2;
  fold (raw_cat r1 r2 pm y x);
}

ghost
fn av_either (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (s: FS.set asn1_id_t) (f1: JF.av_t r1 s) (f2: JF.av_t r2 s)
  (pm: perm) (y: either t1 t2) (x: Ghost.erased SB.bytes)
requires raw_either r1 r2 pm y x
ensures raw_either r1 r2 pm y x ** pure (SL.avoids s x)
{
  match y {
    Inl a -> {
      rewrite (raw_either r1 r2 pm y x) as (r1 pm a x);
      f1 pm a x;
      rewrite (r1 pm a x) as (raw_either r1 r2 pm y x);
    }
    Inr b -> {
      rewrite (raw_either r1 r2 pm y x) as (r2 pm b x);
      f2 pm b x;
      rewrite (r2 pm b x) as (raw_either r1 r2 pm y x);
    }
  }
}

let av_dlit (kid: asn1_id_t) (#key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (#y: asn1_gen_items_lk) (#t: Type0) (di: idesc (dsnd y) t)
  (s: FS.set asn1_id_t) (sq: squash (FS.disjoint s (FS.singleton kid)))
: JF.av_t (raw_dlit kid kx #y di) s
= key_framed kid key_k kx;
  fun pm z x -> av_pre_framed (WA.raw_key_enc kid key_k kx) (raw_irel false di) s (FS.singleton kid) () pm z x

let rec av_sxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (d: sxdesc key_k ls t)
  (s: FS.set asn1_id_t) (sq: squash (FS.disjoint s (FS.singleton kid)))
: Tot (JF.av_t (raw_sxrel kid d) s) (decreases d)
= match d with
  | SX_NIL _ ->
    adb_nil_equiv kid key_k;
    JF.av_ext (raw_false unit) (raw_sxrel kid d) () s (av_false unit s)
  | SX_SINGLE _ kx y di ->
    adb_single_equiv kid kx y di;
    JF.av_ext (raw_dlit kid kx #y di) (raw_sxrel kid d) () s (av_dlit kid kx di s ())
  | SX_CONS _ kx y di dtl ->
    adb_cons_equiv kid kx y di dtl;
    JF.av_ext (raw_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl)) (raw_sxrel kid d) () s
      (fun pm z x -> av_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl) s (av_dlit kid kx di s ()) (av_sxrel kid dtl s ()) pm z x)

let av_dfbr (kid: asn1_id_t) (key_k: asn1_terminal_k) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (s: FS.set asn1_id_t) (sq: squash (FS.disjoint s (FS.singleton kid)))
: JF.av_t (raw_dfbr kid key_k dfb) s
= fun pm z x -> av_cat_fr (raw_terminal_rel kid key_k) (raw_irel false dfb) s (FS.singleton kid) () (JF.fr_terminal kid key_k) pm z x

let rec av_fxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#fbt: Type0) (#t: Type0) (d: fxdesc key_k ls fbt t)
  (fbr: bprel fbt) (s: FS.set asn1_id_t) (sq: squash (FS.disjoint s (FS.singleton kid))) (avf: JF.av_t fbr s)
: Tot (JF.av_t (raw_fxrel kid d fbr) s) (decreases d)
= match d with
  | FX_NIL _ ->
    afb_nil_equiv kid key_k fbr;
    JF.av_ext fbr (raw_fxrel kid d fbr) () s avf
  | FX_SINGLE _ kx y di ->
    afb_single_equiv kid kx y di fbr;
    JF.av_ext (raw_either (raw_dlit kid kx #y di) fbr) (raw_fxrel kid d fbr) () s
      (fun pm z x -> av_either (raw_dlit kid kx #y di) fbr s (av_dlit kid kx di s ()) avf pm z x)
  | FX_CONS _ kx y di dtl ->
    afb_cons_equiv kid kx y di dtl fbr;
    JF.av_ext (raw_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr)) (raw_fxrel kid d fbr) () s
      (fun pm z x -> av_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr) s (av_dlit kid kx di s ()) (av_fxrel kid dtl fbr s () avf) pm z x)

(* The prefix items, then the suffix, whose raw bytes avoid any set of
   identifiers disjoint from `ks` *)

let av_sfx_t (#sfx: Type0) (sr: bprel sfx) (ks: FS.set asn1_id_t) =
  (s: FS.set asn1_id_t) -> squash (FS.disjoint s ks) -> JF.av_t sr s

#push-options "--fuel 2 --ifuel 2 --z3rlimit 32"
let rec av_iarel (#i: id_decs) (#ls: asn1_gen_items_l i) (#sfx: Type0) (#t: Type0) (d: iadesc ls sfx t) (ks: FS.set asn1_id_t) (s: FS.set asn1_id_t)
  (wf: squash (asn1_any_prefix_k_wf' ks i s))
  (sr: bprel sfx) (avs: av_sfx_t sr ks)
: Tot (JF.av_t (raw_iarel d sr) s) (decreases d)
= match d with
  | IA_NIL ->
    items_any_nil_equiv sr;
    JF.av_ext sr (raw_iarel d sr) () s (avs s ())
  | IA_SINGLE #s1 #d1 #dk dd ->
    items_any_single_equiv dd sr;
    L.item_set_twin dk;
    SL.item_dec_twin dk;
    if JF.any_dec dk
    then JF.av_none (raw_iarel d sr) s ()
    else if PLAIN? d1
    then JF.av_ext (raw_cat (raw_drel dd) sr) (raw_iarel d sr) () s
      (fun pm y x -> JF.av_cons_plain (raw_drel dd) sr (In.twin_of dk) s () (JF.fe_drel dd ()) pm y x)
    else JF.av_ext (raw_cat (raw_drel dd) sr) (raw_iarel d sr) () s
      (fun pm y x -> JF.av_cons_opt (raw_drel dd) sr (In.twin_of dk) s (FS.union s s1) () (JF.fe_drel dd ())
        (avs (FS.union s s1) ()) pm y x)
  | IA_CONS #s1 #d1 #dk dd dtl ->
    items_any_cons_equiv dd dtl sr;
    L.item_set_twin dk;
    SL.item_dec_twin dk;
    if JF.any_dec dk
    then JF.av_none (raw_iarel d sr) s ()
    else if PLAIN? d1
    then JF.av_ext (raw_cat (raw_drel dd) (raw_iarel dtl sr)) (raw_iarel d sr) () s
      (fun pm y x -> JF.av_cons_plain (raw_drel dd) (raw_iarel dtl sr) (In.twin_of dk) s () (JF.fe_drel dd ()) pm y x)
    else JF.av_ext (raw_cat (raw_drel dd) (raw_iarel dtl sr)) (raw_iarel d sr) () s
      (fun pm y x -> JF.av_cons_opt (raw_drel dd) (raw_iarel dtl sr) (In.twin_of dk) s (FS.union s s1) () (JF.fe_drel dd ())
        (av_iarel dtl ks (FS.union s s1) () sr avs) pm y x)
#pop-options

let av_sfx_sxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#t: Type0) (d: sxdesc key_k ls t)
: av_sfx_t (raw_sxrel kid d) (FS.singleton kid)
= fun s sq -> av_sxrel kid d s sq

let av_sfx_fxrel (kid: asn1_id_t) (#key_k: asn1_terminal_k) (#ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#gfb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd gfb) tfb)
  (#t: Type0) (d: fxdesc key_k ls (asn1_terminal_impl_t key_k & tfb) t)
: av_sfx_t (raw_fxrel kid d (raw_dfbr kid key_k dfb)) (FS.singleton kid)
= fun s sq -> av_fxrel kid d (raw_dfbr kid key_k dfb) s sq (av_dfbr kid key_k dfb s sq)
