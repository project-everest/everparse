module ASN1.Pulse.JitWriter
#lang-pulse

(* Checked raw writers with just-in-time checks.

   `check_write_jit_k` has the same specification as
   `ASN1.Pulse.RawWriter.check_write_raw_k`, but instead of validating the
   whole output after writing it, it checks each chunk while writing it:

   - TLVs of PREFIXED types and SEQUENCEs, CHOICEs, and SEQUENCE
     components are checked structurally: their framing is correct by
     construction, so only the presence and order of the components of
     SEQUENCEs need to be checked, by reading the identifier of the first
     component of each nonempty suffix;
   - all other chunks (terminals, SET, SEQUENCE OF, SET OF, ANY, DEFAULT
     components) are validated locally, right after being written, within
     their own bounds.

   So each byte is validated at most once, while it is still in the cache.
   If a check fails, or if the output buffer is too small, the JIT writer
   gives up, and `check_write_jit_k` falls back to `check_write_raw_k` to
   distinguish CW_INVALID from CW_NO_SPACE. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.IdentifierU32.Enc
open ASN1.Spec.ILC
open ASN1.Spec.Sequence
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.RawRel

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module SB = LowParse.Spec.Base
module LPS = LowParse.Pulse.Base
module W = LowParse.Pulse.R2L
module WL = ASN1.Pulse.WriteLeaf
module PS = ASN1.Pulse.ParseSequence
module Sq = ASN1.Pulse.Sequence
module Conf = ASN1.Spec.Conformance
module Ser = ASN1.Spec.Serializer
module In = ASN1.Pulse.Interpreter
module CW = ASN1.Pulse.CheckedWriter
module RW = ASN1.Pulse.RawWriter
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC
module L = ASN1.Pulse.JitWriter.Lemmas

(* A JIT writer either writes `x` and checks that it satisfies `a`, or gives
   up, leaving the output after `p` untouched *)

let jit_post (x: SB.bytes) (a: prop) (p: nat) (v: SB.bytes) (res: bool) (p': nat) (v': SB.bytes) : prop =
  Seq.length v' == Seq.length v /\
  p <= Seq.length v /\
  Seq.slice v' p (Seq.length v) == Seq.slice v p (Seq.length v) /\
  (res == true ==> (W.r2l_post x p v true p' v' /\ a))

inline_for_extraction
let jw (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) =
  (x': t) -> (#x: Ghost.erased SB.bytes) ->
  (out: S.slice U8.t) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt bool
    (pts_to out v ** pts_to pos p ** r pm x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** r pm x' x **
      pure (jit_post x (a x) (SZ.v p) v res (SZ.v p') v'))

let frame_trans (p: nat) (v: SB.bytes) (p1: nat) (v1: SB.bytes) (v2: SB.bytes)
: Lemma
  (requires (p1 <= p /\ p <= Seq.length v /\ Seq.length v1 == Seq.length v /\ Seq.length v2 == Seq.length v /\
    Seq.slice v1 p (Seq.length v) == Seq.slice v p (Seq.length v) /\
    Seq.slice v2 p1 (Seq.length v) == Seq.slice v1 p1 (Seq.length v)))
  (ensures (Seq.slice v2 p (Seq.length v) == Seq.slice v p (Seq.length v)))
= let n = Seq.length v in
  Seq.slice_slice v1 p1 n (p - p1) (n - p1);
  Seq.slice_slice v2 p1 n (p - p1) (n - p1)

(* Combinators *)

inline_for_extraction
fn jit_ext (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2))
  (a1 a2: SB.bytes -> prop) (imp: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a2 x)))
  (pm: perm) (w: jw r1 a1 pm)
: jw #t r2 a2 pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  rewrite (r2 pm x' x) as (r1 pm x' x);
  let res = w x' #x out pos;
  rewrite (r1 pm x' x) as (r2 pm x' x);
  if res {
    imp x;
    true
  } else {
    false
  }
}

let local_correct (#k: parser_kind) (#t: Type) (pp: SB.parser k t) (x: SB.bytes) (v1: SB.bytes) (p1: SZ.t) (p0: nat) (off: SZ.t) (valid: bool)
: Lemma
  (requires (SZ.v p1 <= p0 /\ p0 <= Seq.length v1 /\ Seq.slice v1 (SZ.v p1) p0 == x /\
    LPS.validator_postcond pp p1 (Seq.slice v1 0 p0) off valid /\ valid == true /\ SZ.v off == p0))
  (ensures (L.acc pp x))
= Seq.slice_slice v1 0 p0 (SZ.v p1) p0

(* Write with a raw writer, then validate what was written, within its
   bounds *)
inline_for_extraction
fn jit_local (#t: Type0) (r: bprel t) (pm: perm) (w: RW.rw r pm)
  (#tp: Type0) (#k: Ghost.erased parser_kind) (#pp: SB.parser k tp) (vf: LPS.validator #tp #k pp)
: jw #t r (L.acc pp) pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let p0 = !pos;
  let ok = w x' #x out pos;
  if ok {
    with v1 . assert (pts_to out v1);
    let p1 = !pos;
    let sp = S.split out p0;
    match sp {
      Mktuple2 s1 s2 -> {
        let mut off = p1;
        let valid = vf s1 off;
        let off1 = !off;
        S.join s1 s2 out;
        Seq.lemma_split v1 (SZ.v p0);
        rewrite (pts_to out (Seq.append (Seq.slice v1 0 (SZ.v p0)) (Seq.slice v1 (SZ.v p0) (Seq.length v1))))
          as (pts_to out v1);
        if (valid && off1 = p0) {
          local_correct pp x v1 p1 (SZ.v p0) off1 valid;
          true
        } else {
          false
        }
      }
    }
  } else {
    false
  }
}

inline_for_extraction
fn jit_tlv (id: asn1_id_t) (#t: Type0) (r: bprel t)
  (#ack: asn1_content_k) (pp: asn1_weak_parser (asn1_content_t ack))
  (pm: perm) (w: jw r (L.acc #asn1_weak_parser_kind pp) pm)
: jw #t (raw_tlv id r) (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id #ack pp)) pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_tlv id r pm x' x);
  with c . assert (r pm x' c);
  let p0 = !pos;
  let ok = w x' #c out pos;
  if ok {
    with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
    let p1r = !pos;
    let len = SZ.sub p0 p1r;
    assert_norm (pow2 32 == 4294967296);
    if (SZ.eq (SZ.uint32_to_sizet (SZ.sizet_to_uint32 len)) len) {
      fold (W.vmatch_sz len (Seq.length c));
      let ok2 = WL.r2l_write_hdr true len #(Seq.length c) out pos;
      unfold (W.vmatch_sz len (Seq.length c));
      with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
      frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
      if ok2 {
        let ok3 = WL.r2l_write_id id out pos;
        with v3 p3 . assert (pts_to out v3 ** pts_to pos p3);
        frame_trans (SZ.v p) v (SZ.v p2) v2 v3;
        fold (raw_tlv id r pm x' x);
        if ok3 {
          W.r2l_post_append (enc_hdr true (Seq.length c)) c (SZ.v p) v (SZ.v p1) v1 true (SZ.v p2) v2;
          W.r2l_post_append (asn1_id_enc id) (enc_hdr true (Seq.length c) `Seq.append` c) (SZ.v p) v (SZ.v p2) v2 true (SZ.v p3) v3;
          L.acc_tlv id #ack pp c;
          true
        } else {
          false
        }
      } else {
        fold (raw_tlv id r pm x' x);
        false
      }
    } else {
      fold (raw_tlv id r pm x' x);
      false
    }
  } else {
    fold (raw_tlv id r pm x' x);
    false
  }
}

inline_for_extraction
fn jit_opt (#t: Type0) (r: bprel t) (a1 a2: SB.bytes -> prop)
  (none: squash (a2 Seq.empty))
  (imp: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a2 x)))
  (pm: perm) (w: jw r a1 pm)
: jw #(option t) (raw_opt r) a2 pm
= (x': option t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (raw_opt r pm x' x) as (pure (Ghost.reveal x == Seq.empty));
      W.r2l_post_empty (SZ.v p) v;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt r pm x' x);
      true
    }
    Some y -> {
      rewrite (raw_opt r pm x' x) as (r pm y x);
      let res = w y #x out pos;
      rewrite (r pm y x) as (raw_opt r pm x' x);
      if res {
        imp x;
        true
      } else {
        false
      }
    }
  }
}

inline_for_extraction
fn jit_either (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (a1 a2 a: SB.bytes -> prop)
  (imp1: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a x)))
  (imp2: (x: SB.bytes) -> Lemma (requires (a2 x)) (ensures (a x)))
  (pm: perm) (w1: jw r1 a1 pm) (w2: jw r2 a2 pm)
: jw #(either t1 t2) (raw_either r1 r2) a pm
= (x': either t1 t2) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    Inl y -> {
      rewrite (raw_either r1 r2 pm x' x) as (r1 pm y x);
      let res = w1 y #x out pos;
      rewrite (r1 pm y x) as (raw_either r1 r2 pm x' x);
      if res {
        imp1 x;
        true
      } else {
        false
      }
    }
    Inr y -> {
      rewrite (raw_either r1 r2 pm x' x) as (r2 pm y x);
      let res = w2 y #x out pos;
      rewrite (r2 pm y x) as (raw_either r1 r2 pm x' x);
      if res {
        imp2 x;
        true
      } else {
        false
      }
    }
  }
}

inline_for_extraction
fn jit_false (t: Type0) (a: SB.bytes -> prop) (pm: perm)
: jw #t (raw_false t) a pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_false t pm x' x);
  unreachable ()
}

inline_for_extraction
fn jit_nil (pm: perm)
: jw #unit (raw_pure null_enc) (L.iacc []) pm
= (x': unit) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_pure null_enc pm x' x);
  fold (raw_pure null_enc pm x' x);
  W.r2l_post_empty (SZ.v p) v;
  L.iacc_nil ();
  true
}

(* SEQUENCE components: after writing the head `hd` before the tail `tl`,
   check that the first identifier is that of `hd` if `hd` is present, and
   not that of `hd` if `hd` is absent *)

let ids_ok (s: Set.set asn1_id_t) (v: SB.bytes) (p2 p1 p0: nat) : prop =
  p2 <= p1 /\ p1 <= p0 /\ p0 <= Seq.length v /\
  (p2 < p1 ==> (match L.pid (Seq.slice v p2 (Seq.length v)) with
      | Some (id, _) -> Set.mem id s
      | None -> True)) /\
  ((p2 == p1 /\ p1 < p0) ==> (match L.pid (Seq.slice v p1 (Seq.length v)) with
      | Some (id, _) -> ~ (Set.mem id s)
      | None -> True))

inline_for_extraction
fn check_ids (s: Ghost.erased (Set.set asn1_id_t)) (has_id: (id: asn1_id_t) -> (b: bool { b == Set.mem id s }))
  (out: S.slice U8.t) (p2 p1 p0: SZ.t) (#v: Ghost.erased SB.bytes)
requires pts_to out v ** pure (SZ.v p2 <= SZ.v p1 /\ SZ.v p1 <= SZ.v p0 /\ SZ.v p0 <= Seq.length v)
returns res: bool
ensures pts_to out v ** pure (res == true ==> ids_ok s v (SZ.v p2) (SZ.v p1) (SZ.v p0))
{
  if (SZ.lt p2 p1) {
    let mut off = p2;
    let r = I.vread_identifier out off;
    match r {
      None -> { false }
      Some id -> { has_id id }
    }
  } else if (SZ.lt p1 p0) {
    let mut off = p1;
    let r = I.vread_identifier out off;
    match r {
      None -> { false }
      Some id -> { not (has_id id) }
    }
  } else {
    true
  }
}

let cons_correct (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl })
  (c1 c2: SB.bytes) (p: nat) (v: SB.bytes) (p1: nat) (v1: SB.bytes) (p2: nat) (v2: SB.bytes)
: Lemma
  (requires (W.r2l_post c2 p v true p1 v1 /\ W.r2l_post c1 p1 v1 true p2 v2 /\
    L.iacc [hd] c1 /\ L.iacc tl c2 /\ ids_ok (Sq.item_set hd) v2 p2 p1 p))
  (ensures (W.r2l_post (Seq.append c1 c2) p v true p2 v2 /\ L.iacc (hd :: tl) (Seq.append c1 c2)))
= W.r2l_post_append c1 c2 p v p1 v1 true p2 v2;
  let n = Seq.length v in
  Seq.slice_slice v1 p1 n 0 (p - p1);
  Seq.slice_slice v2 p1 n 0 (p - p1);
  L.iacc_cons hd tl v2 p2 p1 p

inline_for_extraction
fn jit_items_cons (hd: Ghost.erased gen_decorated_parser_twin) (tl: Ghost.erased (list gen_decorated_parser_twin) { Cons? tl })
  (has_id: (id: asn1_id_t) -> (b: bool { b == Set.mem id (Sq.item_set hd) }))
  (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm)
  (w1: jw r1 (L.iacc [Ghost.reveal hd]) pm) (w2: jw r2 (L.iacc tl) pm)
: jw #(t1 & t2) (raw_cat r1 r2) (L.iacc (Ghost.reveal hd :: Ghost.reveal tl)) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_cat r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  let p0 = !pos;
  let ok = w2 (snd x') #c2 out pos;
  if ok {
    with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
    let p1r = !pos;
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    fold (raw_cat r1 r2 pm x' x);
    if res {
      let p2r = !pos;
      let ck = check_ids (Sq.item_set hd) has_id out p2r p1r p0;
      if ck {
        cons_correct hd tl c1 c2 (SZ.v p) v (SZ.v p1) v1 (SZ.v p2) v2;
        true
      } else {
        false
      }
    } else {
      false
    }
  } else {
    fold (raw_cat r1 r2 pm x' x);
    false
  }
}

(* The whole schema *)

let jres (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) (x': t) (x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (v: Ghost.erased SB.bytes) (p: Ghost.erased SZ.t) : Type =
  stt bool
    (pts_to out v ** pts_to pos p ** r pm x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** r pm x' x **
      pure (jit_post x (a x) (SZ.v p) v res (SZ.v p') v'))

let cacc (id: asn1_id_t) (k: asn1_content_k) : SB.bytes -> prop =
  L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser k))

let kacc (#s: _) (k: asn1_k s) : SB.bytes -> prop =
  L.acc #asn1_strong_parser_kind (asn1_as_parser k)

let dacc (#s: _) (#d: _) (dk: asn1_decorated_k s d) : SB.bytes -> prop =
  L.iacc [In.twin_of dk]

let lc_ok (lc: list (asn1_id_t & asn1_content_k)) : prop =
  In.supported_lc lc /\ List.Tot.noRepeats (List.Tot.map fst lc)

[@@In.asn1_pulse_attr]
let rec jit_write_content (id: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k: asn1_content_k) (u: squash (In.supported_content k)) (pm: perm)
  (x': asn1_content_impl_t k) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jres (raw_content_rel id k) (cacc id k) pm x' x out pos v p)
  (decreases k)
= [@inline_let] let vf : jw (raw_content_rel id k) (cacc id k) pm =
  (match k with
  | ASN1_PREFIXED k' ->
    content_prefixed_equiv id k';
    jit_ext (raw_tlv id (raw_rel k')) (raw_content_rel id (ASN1_PREFIXED k')) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_PREFIXED k')))) (cacc id k) (fun _ -> ()) pm
      (jit_tlv id (raw_rel k') (asn1_content_as_parser (ASN1_PREFIXED k')) pm
        (jit_ext (raw_rel k') (raw_rel k') () (kacc k') (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_PREFIXED k'))) (L.acc_prefixed k') pm
          (fun x' #x out pos #v #p -> jit_write_k k' () pm x' #x out pos #v #p)))
  | ASN1_SEQUENCE gitems ->
    content_sequence_equiv id gitems;
    jit_ext (raw_tlv id (raw_items_rel false (dsnd gitems))) (raw_content_rel id (ASN1_SEQUENCE gitems)) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_SEQUENCE gitems)))) (cacc id k) (fun _ -> ()) pm
      (jit_tlv id (raw_items_rel false (dsnd gitems)) (asn1_content_as_parser (ASN1_SEQUENCE gitems)) pm
        (jit_ext (raw_items_rel false (dsnd gitems)) (raw_items_rel false (dsnd gitems)) ()
          (L.iacc (In.twins_of (dsnd gitems))) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE gitems))) (L.acc_sequence gitems) pm
          (fun x' #x out pos #v #p -> jit_write_items (dsnd gitems) () pm x' #x out pos #v #p)))
  | _ ->
    jit_local (raw_content_rel id k) pm
      (fun x' #x out pos #v #p -> RW.raw_write_content id k pm x' #x out pos #v #p)
      (ILC.validate_asn1_ILC id (In.validate_content k ())))
  in vf x' #x out pos #v #p

and jit_write_items (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (In.supported_items ls)) (pm: perm)
  (x': asn1_items_impl_t ls) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jres (raw_items_rel false ls) (L.iacc (In.twins_of ls)) pm x' x out pos v p)
  (decreases ls)
= [@inline_let] let vf : jw (raw_items_rel false ls) (L.iacc (In.twins_of ls)) pm =
  (match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_nil_equiv false;
    jit_ext (raw_pure null_enc) (raw_items_rel false ASN1_GEN_ITEMS_NIL) ()
      (L.iacc []) (L.iacc (In.twins_of ls)) (fun _ -> ()) pm (jit_nil pm)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    items_single_equiv false dk;
    L.twins_of_single dk;
    jit_ext (raw_dec_rel dk) (raw_items_rel false (PS.single dk)) ()
      (dacc dk) (L.iacc (In.twins_of ls)) (fun _ -> ()) pm
      (fun x' #x out pos #v #p -> jit_write_dec dk () pm x' #x out pos #v #p)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_cons_equiv false dk dk2 tl2;
    join_cat_equiv false (raw_dec_rel dk) (raw_items_rel false (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2));
    L.twins_of_cons2 dk dk2 tl2;
    jit_ext
      #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
      (raw_cat (raw_dec_rel dk) (raw_items_rel false (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
      (raw_items_rel false (PS.cons2 dk dk2 tl2)) ()
      (L.iacc (In.twin_of dk :: In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (L.iacc (In.twins_of ls)) (fun _ -> ()) pm
      (jit_items_cons (In.twin_of dk) (In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (In.has_id_dec dk ())
        (raw_dec_rel dk) (raw_items_rel false (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) pm
        (fun x' #x out pos #v #p -> jit_write_dec dk () pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> jit_write_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) () pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and jit_write_dec (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] d: _) ([@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s d) (u: squash (In.supported_dec dk)) (pm: perm)
  (x': asn1_decorated_impl_t dk) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jres (raw_dec_rel dk) (dacc dk) pm x' x out pos v p)
  (decreases dk)
= [@inline_let] let vf : jw (raw_dec_rel dk) (dacc dk) pm =
  (match dk with
  | ASN1_PLAIN_ILC k ->
    dec_plain_equiv k;
    jit_ext (raw_rel k) (raw_dec_rel (ASN1_PLAIN_ILC k)) () (kacc k) (dacc dk) (L.iacc_plain k) pm
      (fun x' #x out pos #v #p -> jit_write_k k () pm x' #x out pos #v #p)
  | ASN1_OPTION_ILC k ->
    dec_option_equiv k;
    L.iacc_option_none k;
    jit_ext (raw_opt (raw_rel k)) (raw_dec_rel (ASN1_OPTION_ILC k)) () (dacc dk) (dacc dk) (fun _ -> ()) pm
      (jit_opt (raw_rel k) (kacc k) (dacc dk) () (L.iacc_option_some k) pm
        (fun x' #x out pos #v #p -> jit_write_k k () pm x' #x out pos #v #p))
  | _ ->
    L.twins_of_single dk;
    jit_ext (raw_dec_rel dk) (raw_dec_rel dk) () (L.iacc (In.twins_of (PS.single dk))) (dacc dk) (fun _ -> ()) pm
      (jit_local (raw_dec_rel dk) pm
        (fun x' #x out pos #v #p -> RW.raw_write_dec dk pm x' #x out pos #v #p)
        (In.validate_seq (PS.single dk) (L.supported_single dk ()) None)))
  in vf x' #x out pos #v #p

and jit_write_k (#[@@@FStar.Attributes.monomorphize] s: _) ([@@@FStar.Attributes.monomorphize] k: asn1_k s) (u: squash (In.supported_k k)) (pm: perm)
  (x': asn1_impl_t k) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jres (raw_rel k) (kacc k) pm x' x out pos v p)
  (decreases k)
= [@inline_let] let vf : jw (raw_rel k) (kacc k) pm =
  (match k with
  | ASN1_ILC id k' ->
    rel_ilc_equiv id k';
    jit_ext (raw_content_rel id k') (raw_rel (ASN1_ILC id k')) () (cacc id k') (kacc k) (L.acc_k_ilc id k') pm
      (fun x' #x out pos #v #p -> jit_write_content id k' () pm x' #x out pos #v #p)
  | ASN1_CHOICE_ILC lc pf ->
    rel_choice_equiv lc pf;
    jit_ext (raw_lc_rel lc) (raw_rel (ASN1_CHOICE_ILC lc pf)) () (L.lacc lc) (kacc k) (L.lacc_choice lc pf) pm
      (fun x' #x out pos #v #p -> jit_write_lc lc () pm x' #x out pos #v #p)
  | ASN1_ANY_ILC ->
    rel_any_equiv ();
    jit_ext raw_slice (raw_rel ASN1_ANY_ILC) () (kacc k) (kacc k) (fun _ -> ()) pm
      (jit_local raw_slice pm (RW.raw_write_slice pm) (In.validate_k ASN1_ANY_ILC ())))
  in vf x' #x out pos #v #p

and jit_write_lc ([@@@FStar.Attributes.monomorphize] lc: list (asn1_id_t & asn1_content_k)) (u: squash (lc_ok lc)) (pm: perm)
  (x': asn1_lc_impl_t lc) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jres (raw_lc_rel lc) (L.lacc lc) pm x' x out pos v p)
  (decreases lc)
= [@inline_let] let vf : jw (raw_lc_rel lc) (L.lacc lc) pm =
  (match lc with
  | [] ->
    lc_nil_equiv ();
    jit_ext (raw_false unit) (raw_lc_rel []) () (L.lacc lc) (L.lacc lc) (fun _ -> ()) pm (jit_false unit (L.lacc lc) pm)
  | [(id', c)] ->
    lc_single_equiv id' c;
    let u' = L.lc_tail_ok (id', c) [] u in
    jit_ext (raw_content_rel id' c) (raw_lc_rel [(id', c)]) () (cacc id' c) (L.lacc lc) (L.lacc_hd id' c []) pm
      (fun x' #x out pos #v #p -> jit_write_content id' c () pm x' #x out pos #v #p)
  | (id', c) :: hd2 :: tl2 ->
    lc_cons_equiv id' c hd2 tl2;
    let u' = L.lc_tail_ok (id', c) (hd2 :: tl2) u in
    jit_ext (raw_either (raw_content_rel id' c) (raw_lc_rel (hd2 :: tl2))) (raw_lc_rel ((id', c) :: hd2 :: tl2)) () (L.lacc lc) (L.lacc lc) (fun _ -> ()) pm
      (jit_either (raw_content_rel id' c) (raw_lc_rel (hd2 :: tl2)) (cacc id' c) (L.lacc (hd2 :: tl2)) (L.lacc lc)
        (L.lacc_hd id' c (hd2 :: tl2)) (L.lacc_tl id' c (hd2 :: tl2)) pm
        (fun x' #x out pos #v #p -> jit_write_content id' c () pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> jit_write_lc (hd2 :: tl2) () pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

(* The top level *)

inline_for_extraction
let jit_writer (#s: _) (k: asn1_k s) (u: squash (RW.raw_ok k)) (pm: perm) : jw (raw_rel k) (kacc k) pm =
  fun x' #x out pos #v #p -> jit_write_k k () pm x' #x out pos #v #p

let jit_ok_correct (#s: _) (k: asn1_k s) (enc: SB.bytes) (p: nat) (v: SB.bytes) (p': nat) (v': SB.bytes)
: Lemma
  (requires (Conf.wf k /\ jit_post enc (kacc k enc) p v true p' v'))
  (ensures (CW.cw_post k enc p v CW.CW_OK p' v'))
= Ser.parsed_spec_correct k enc;
  assert (Seq.equal (Seq.slice enc 0 (Seq.length enc)) enc)

(* `wj`, `w` and `vf` are meant to be `jit_writer k u pm`,
   `RW.raw_writer k pm` and `RW.raw_validator k u`, passed by the
   extraction root *)
inline_for_extraction
fn check_write_jit_k (#s: _) (k: asn1_k s) (u: squash (RW.raw_ok k)) (pm: perm)
  (wj: jw (raw_rel k) (kacc k) pm)
  (w: RW.rw (raw_rel k) pm)
  (vf: LPS.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k))
: RW.checked_raw_writer_t k pm
= (x': asn1_impl_t k) (#y: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let p0 = !pos;
  let ok = wj x' #y out pos;
  with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
  if ok {
    jit_ok_correct k y (SZ.v p) v (SZ.v p1) v1;
    CW.CW_OK
  } else {
    pos := p0;
    let res = RW.check_write_raw_k k u pm w vf x' #y out pos;
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p) v1 v2;
    res
  }
}
