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
   - SEQUENCE OF and SET OF are checked element by element: each element
     is checked by its own JIT writer (or, if given already serialized,
     validated on the input slice before being copied) and must be
     nonempty; a SET OF
     element must also be exactly one frame, so that inserting it keeps
     the elements sorted; finally the SIZE (1..MAX) constraint is checked;
   - SET is checked component by component: each component is checked by
     its own JIT writer and must be either empty or exactly one frame
     whose identifier belongs to the component, so that inserting it keeps
     the components sorted; since the tags of distinct components are
     disjoint, the result is then strictly sorted, with each component at
     most once;
   - terminals, RESTRICTED terminals, and DEFAULT components of leaf
     type are checked on the input value, before writing anything
     (`ASN1.Pulse.JitTerminal`): string contents, BOOLEAN and NULL
     contents, BIT STRING padding, INTEGER minimality (or, for small
     INTEGERs, the range of the machine integer), restrictions, and
     disequality with the DEFAULT value; their TLV is then correct by
     construction. No scratch buffer is used;
   - ANY values are validated on the input slice, before being copied;
   - DEFAULT components of PREFIXED type are validated locally, right
     after being written, within their own bounds. (ANY DEFINED BY is
     not supported by the raw writers.)

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
module It = LowParse.PulseParse.Iterator
module WI = LowParse.PulseParse.Iterator.R2L
module PB = LowParse.PulseParse.Base
module SI = ASN1.Pulse.SortedInsert
module Trade = Pulse.Lib.Trade.Util
module E = ASN1.Spec.Content.Enc
module Co = ASN1.Pulse.Constructed
module JT = ASN1.Pulse.JitTerminal
open Pulse.Lib.Trade

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

(* SET components: each component is written and checked on its own: it
   must be either empty (an absent OPTIONAL or DEFAULT component) or exactly
   one frame whose identifier is one of those of the component; then it is
   inserted at its sorted position into the components written so far. The
   disjointness of the tags of the components (`asn1_set_k_wf`) then
   ensures that the result is strictly sorted, each component appearing at
   most once. *)

inline_for_extraction
fn check_elt (s: Ghost.erased (Set.set asn1_id_t)) (has_id: (id: asn1_id_t) -> (b: bool { b == Set.mem id s }))
  (out: S.slice U8.t) (p2 p1: SZ.t) (#v: Ghost.erased SB.bytes)
requires pts_to out v ** pure (SZ.v p2 <= SZ.v p1 /\ SZ.v p1 <= Seq.length v)
returns res: bool
ensures pts_to out v ** pure (SZ.v p2 <= SZ.v p1 /\ SZ.v p1 <= Seq.length v /\ (res == true ==> L.elt_ok s (Seq.slice v (SZ.v p2) (SZ.v p1))))
{
  if (SZ.lt p2 p1) {
    let n = SI.read_frame out p2 p1;
    if (n = SZ.sub p1 p2) {
      let a = SI.read_id out p2 p1;
      match a {
        None -> { false }
        Some id -> { has_id id }
      }
    } else {
      false
    }
  } else {
    true
  }
}

inline_for_extraction
fn jit_set_elt (hd: Ghost.erased gen_decorated_parser_twin)
  (has_id: (id: asn1_id_t) -> (b: bool { b == Set.mem id (Sq.item_set hd) }))
  (#t: Type0) (r: bprel t) (pm: perm) (w: jw r (L.iacc [Ghost.reveal hd]) pm)
: jw #t r (L.sacc1 hd) pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let p0 = !pos;
  let res = w x' #x out pos;
  if res {
    let p2 = !pos;
    check_elt (Sq.item_set hd) has_id out p2 p0
  } else {
    false
  }
}

inline_for_extraction
fn jit_set_cons (hd: Ghost.erased gen_decorated_parser_twin) (tl: Ghost.erased (list gen_decorated_parser_twin))
  (sq: squash (L.set_cons_ok hd tl))
  (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm)
  (w1: jw r1 (L.sacc1 hd) pm) (w2: jw r2 (L.sacc tl) pm)
: jw #(t1 & t2) (raw_ins SI.lt_tag r1 r2) (L.sacc (Ghost.reveal hd :: Ghost.reveal tl)) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_ins SI.lt_tag r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  let p0 = !pos;
  let ok = w2 (snd x') #c2 out pos;
  if ok {
    with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
    let p1r = !pos;
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    if res {
      let p2r = !pos;
      SI.r2l_insert SI.lt_tag (SI.lt_tag_impl ()) out p2r p1r p0;
      with v3 . assert (pts_to out v3);
      SI.r2l_post_ins SI.lt_tag c1 c2 (SZ.v p) v (SZ.v p1) v1 (SZ.v p2) v2 v3;
      L.sacc_cons hd tl c1 c2;
      fold (raw_ins SI.lt_tag r1 r2 pm x' x);
      true
    } else {
      fold (raw_ins SI.lt_tag r1 r2 pm x' x);
      false
    }
  } else {
    fold (raw_ins SI.lt_tag r1 r2 pm x' x);
    false
  }
}

(* SEQUENCE OF and SET OF: each element is written and checked on its own
   (an element given as a structure by its own JIT writer, an already
   serialized element by validating it on the input slice before copying
   it), and must be nonempty; then, as in
   `LowParse.PulseParse.Iterator.R2L.r2l_write_mixed_list_gen` (resp.
   `ASN1.Pulse.SortedInsert.r2l_write_mixed_list_sorted_gen`), it is
   reversed (resp. inserted into the elements written so far). For a
   SET OF, each element is also checked to be exactly one frame, so that
   the insertion keeps the elements sorted. Finally, the SIZE (1..MAX)
   constraint is checked on the size of the result. *)

inline_for_extraction
fn jit_pre (#t: Type0) (r: bprel t) (a a': SB.bytes -> prop)
  (imp: (x: SB.bytes) -> Lemma (requires (a x)) (ensures (a' x)))
  (pm: perm) (c: JT.pcg r JT.ptrue a pm) (w: RW.rw r pm)
: jw #t r a' pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let ok = c x' #x;
  if ok {
    imp x;
    w x' #x out pos
  } else {
    false
  }
}

let ser_rel (pm: perm) (pl: S.slice U8.t) (y: SB.bytes) : slprop =
  PB.pts_to_parsed p_raw pl #pm y

inline_for_extraction
fn raw_write_ser (pm: perm)
: RW.rw #(S.slice U8.t) ser_rel pm
= (x': S.slice U8.t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (ser_rel pm x' x);
  unfold (PB.pts_to_parsed p_raw x' #pm x);
  with wb . assert (S.pts_to x' #pm wb);
  p_raw_consumed wb x;
  fold (W.vmatch_bytes pm x' wb);
  let res = W.r2l_write_copy pm x' #wb out pos;
  unfold (W.vmatch_bytes pm x' wb);
  fold (PB.pts_to_parsed p_raw x' #pm x);
  fold (ser_rel pm x' x);
  res
}

(* Validate an already serialized element on the input slice, before
   copying it *)
inline_for_extraction
fn pc_ser (#tp: Type0) (#kk: Ghost.erased parser_kind) (#pp: SB.parser kk tp) (vf: LPS.validator #tp #kk pp) (pm: perm)
: JT.pcg #(S.slice U8.t) ser_rel JT.ptrue (L.acc pp) pm
= (pl: S.slice U8.t) (#x: Ghost.erased SB.bytes)
{
  unfold (ser_rel pm pl x);
  unfold (PB.pts_to_parsed p_raw pl #pm x);
  with wb . assert (S.pts_to pl #pm wb);
  p_raw_consumed wb x;
  S.pts_to_len pl;
  let mut off = 0sz;
  let valid = vf pl off;
  let off1 = !off;
  fold (PB.pts_to_parsed p_raw pl #pm x);
  fold (ser_rel pm pl x);
  if (valid && (off1 = S.len pl)) {
    JT.acc_of_valid pp wb off1;
    true
  } else {
    false
  }
}

inline_for_extraction
fn jit_elt (#t: Type0) (r: bprel t)
  (#tp: Type0) (#pp: asn1_strong_parser tp) (vf: LPS.validator #tp #asn1_strong_parser_kind pp)
  (w: (pm: perm) -> jw r (L.acc #asn1_strong_parser_kind pp) pm)
  (pm: perm)
: jw #(WI.elt_or_serialized t) (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw) (L.acc #asn1_strong_parser_kind pp) pm
= (x': WI.elt_or_serialized t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    WI.EElement e -> {
      rewrite (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm x' x) as (r pm e x);
      let res = w pm e #x out pos;
      rewrite (r pm e x) as (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm x' x);
      res
    }
    WI.ESerialized pl -> {
      rewrite (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm x' x) as (ser_rel pm pl x);
      let res = jit_pre ser_rel (L.acc #asn1_strong_parser_kind pp) (L.acc #asn1_strong_parser_kind pp) (fun _ -> ()) pm (pc_ser #tp #asn1_strong_parser_kind #pp vf pm) (raw_write_ser pm) pl #x out pos;
      rewrite (ser_rel pm pl x) as (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm x' x);
      res
    }
  }
}

let jml_frame (p0: nat) (v0 vc: SB.bytes) : prop =
  Seq.length vc == Seq.length v0 /\ p0 <= Seq.length v0 /\
  Seq.slice vc p0 (Seq.length v0) == Seq.slice v0 p0 (Seq.length v0)

let jml_inv (#tp: Type) (pp: asn1_strong_parser tp) (l: list SB.bytes) (p0: nat) (v0: SB.bytes) (ld: list SB.bytes) (ok: bool) (pc: nat) (vc: SB.bytes) : prop =
  jml_frame p0 v0 vc /\
  (ok == true ==> (WI.r2l_ml_inv id_enc l p0 v0 ld true pc vc /\ L.all_eacc pp ld))

let jsml_inv (#tp: Type) (pp: asn1_strong_parser tp) (l: list SB.bytes) (p0: nat) (v0: SB.bytes) (ld: list SB.bytes) (ok: bool) (pc: nat) (vc: SB.bytes) : prop =
  jml_frame p0 v0 vc /\
  (ok == true ==> (SI.r2l_mls_inv SI.lt_lex id_enc l p0 v0 ld true pc vc /\ L.sf pp None (SI.sort_list SI.lt_lex id_enc ld)))

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"

inline_for_extraction
fn jit_write_ml (#t: Type0) (r: bprel t) (ne: bool)
  (#tp: Type0) (#pp: asn1_strong_parser tp) (vf: LPS.validator #tp #asn1_strong_parser_kind pp)
  (w: (pm: perm) -> jw r (L.acc #asn1_strong_parser_kind pp) pm)
  (sh: share_t r) (g: gather_t r) (pm: perm)
: jw #(ml t) (raw_ml r) (L.acc #asn1_weak_parser_kind (parse_sized_list ne pp)) pm
= (x': ml t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p0: Ghost.erased SZ.t)
{
  unfold (raw_ml r pm x' x);
  with l . assert (WI.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw pm x' l);
  WI.mixed_list_match_length r ml_ops p_raw pm x' l;
  let n0 = LowParse.PulseParse.Iterator.Type.mixed_list_length ml_ops x';
  let it0 = WI.iterator_start r ml_ops p_raw RW.jump_raw pm x' l sh g;
  with pm0 . assert (WI.iterator_match r ml_ops p_raw pm0 it0 l);
  let mut pit = it0;
  let mut pn = n0;
  let mut pok = true;
  WI.r2l_ml_inv_init id_enc l (SZ.v p0) v;
  let p0r = !pos;
  let mut pld : Ghost.erased (list SB.bytes) = Ghost.hide [];
  while (
    let ok = !pok;
    let n = !pn;
    (ok && not (ml_ops.eq n ml_ops.zero))
  ) invariant exists* (it: LowParse.PulseParse.Iterator.Type.iterator SZ.t t) (pmi: perm) (ld: Ghost.erased (list SB.bytes)) (lr: list SB.bytes) (n: SZ.t) (ok: bool) (vc: SB.bytes) (pc: SZ.t) .
    R.pts_to pit it ** R.pts_to pld ld **
    WI.iterator_match r ml_ops p_raw pmi it lr **
    trade (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l) **
    R.pts_to pn n ** R.pts_to pok ok **
    pts_to out vc ** R.pts_to pos pc **
    pure (
      Ghost.reveal l == List.Tot.append (Ghost.reveal ld) lr /\
      ml_ops.v n == List.Tot.length lr /\
      SZ.v p0r == SZ.v p0 /\
      jml_inv pp l (SZ.v p0) v (Ghost.reveal ld) ok (SZ.v pc) vc
    )
  decreases %[(if !pok then 1 else 0); ml_ops.v (!pn)]
  {
    with it pmi lr . assert (R.pts_to pit it ** WI.iterator_match r ml_ops p_raw pmi it lr);
    with vc pc . assert (pts_to out vc ** R.pts_to pos pc);
    let ld = !pld;
    let n = !pn;
    let pcur = !pos;
    let xe = WI.iterator_next_eos r ml_ops p_raw RW.jump_raw pmi pit it lr sh g;
    unfold (WI.iterator_next_eos_post r ml_ops p_raw pmi pit it lr xe);
    with pm_v y tl it' pm' . assert (
      WI.elt_or_serialized_match r ml_ops p_raw pm_v xe y **
      R.pts_to pit it' **
      WI.iterator_match r ml_ops p_raw pm' it' tl);
    let res = jit_elt r vf w pm_v xe #y out pos;
    Trade.elim_hyp_l (WI.elt_or_serialized_match r ml_ops p_raw pm_v xe y) (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr);
    Trade.trans (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l);
    WI.append_assoc_singleton #SB.bytes (Ghost.reveal ld) y tl;
    pn := ml_ops.sub n ml_ops.one;
    pld := Ghost.hide (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]);
    with v2 p2 . assert (pts_to out v2 ** R.pts_to pos p2);
    frame_trans (SZ.v p0) v (SZ.v pc) vc v2;
    if res {
      let pnew = !pos;
      if (SZ.lt pnew pcur) {
        WI.r2l_reverse_range out pnew pcur;
        with v3 . assert (pts_to out v3);
        assert (pure (WI.r2l_ml_inv id_enc l (SZ.v p0) v (Ghost.reveal ld) true (SZ.v pc) vc));
        assert (pure (W.r2l_post (id_enc y) (SZ.v pc) vc true (SZ.v p2) v2));
        assert (pure (WI.reverse_range_post v2 (SZ.v p2) (SZ.v pc) v3));
        WI.r2l_ml_inv_step id_enc l (SZ.v p0) v (Ghost.reveal ld) y (SZ.v pc) vc (SZ.v p2) v2 v3;
        assert (pure (L.all_eacc pp (Ghost.reveal ld)));
        assert (pure (L.eacc pp y));
        L.all_eacc_snoc pp (Ghost.reveal ld) y;
        assert (pure (L.all_eacc pp (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y])));
        assert (pure (WI.r2l_ml_inv id_enc l (SZ.v p0) v (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]) true (SZ.v p2) v3));
        assert (pure (jml_frame (SZ.v p0) v v3));
        assert (pure (jml_inv pp l (SZ.v p0) v (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]) true (SZ.v p2) v3));
      } else {
        pok := false;
      }
    } else {
      pok := false;
    }
  };
  with it pmi lr . assert (R.pts_to pit it ** WI.iterator_match r ml_ops p_raw pmi it lr);
  with vc pc . assert (pts_to out vc ** R.pts_to pos pc);
  let ld = !pld;
  Trade.elim (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l);
  fold (raw_ml r pm x' x);
  let ok = !pok;
  if ok {
    List.Tot.append_l_nil (Ghost.reveal ld);
    let pend = !pos;
    if (ne && not (SZ.lt pend p0r)) {
      false
    } else {
      WI.r2l_reverse_range out pend p0r;
      with v3 . assert (pts_to out v3);
      WI.r2l_ml_inv_end id_enc l (SZ.v p0) v (SZ.v pc) vc v3;
      L.acc_sized_list ne pp l;
      true
    }
  } else {
    false
  }
}

inline_for_extraction
fn jit_write_ml_sorted (#t: Type0) (r: bprel t) (ne: bool)
  (#tp: Type0) (#pp: asn1_strong_parser tp) (vf: LPS.validator #tp #asn1_strong_parser_kind pp)
  (w: (pm: perm) -> jw r (L.acc #asn1_strong_parser_kind pp) pm)
  (sh: share_t r) (g: gather_t r) (pm: perm)
: jw #(ml t) (raw_ml_sorted r) (L.acc #asn1_weak_parser_kind (parse_sized_set ne pp)) pm
= (x': ml t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p0: Ghost.erased SZ.t)
{
  unfold (raw_ml_sorted r pm x' x);
  with l . assert (WI.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw pm x' l);
  WI.mixed_list_match_length r ml_ops p_raw pm x' l;
  let n0 = LowParse.PulseParse.Iterator.Type.mixed_list_length ml_ops x';
  let it0 = WI.iterator_start r ml_ops p_raw RW.jump_raw pm x' l sh g;
  with pm0 . assert (WI.iterator_match r ml_ops p_raw pm0 it0 l);
  let mut pit = it0;
  let mut pn = n0;
  let mut pok = true;
  SI.r2l_mls_inv_init SI.lt_lex id_enc l (SZ.v p0) v;
  L.sf_empty pp;
  let p0r = !pos;
  let mut pld : Ghost.erased (list SB.bytes) = Ghost.hide [];
  while (
    let ok = !pok;
    let n = !pn;
    (ok && not (ml_ops.eq n ml_ops.zero))
  ) invariant exists* (it: LowParse.PulseParse.Iterator.Type.iterator SZ.t t) (pmi: perm) (ld: Ghost.erased (list SB.bytes)) (lr: list SB.bytes) (n: SZ.t) (ok: bool) (vc: SB.bytes) (pc: SZ.t) .
    R.pts_to pit it ** R.pts_to pld ld **
    WI.iterator_match r ml_ops p_raw pmi it lr **
    trade (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l) **
    R.pts_to pn n ** R.pts_to pok ok **
    pts_to out vc ** R.pts_to pos pc **
    pure (
      Ghost.reveal l == List.Tot.append (Ghost.reveal ld) lr /\
      ml_ops.v n == List.Tot.length lr /\
      SZ.v p0r == SZ.v p0 /\
      jsml_inv pp l (SZ.v p0) v (Ghost.reveal ld) ok (SZ.v pc) vc
    )
  decreases %[(if !pok then 1 else 0); ml_ops.v (!pn)]
  {
    with it pmi lr . assert (R.pts_to pit it ** WI.iterator_match r ml_ops p_raw pmi it lr);
    with vc pc . assert (pts_to out vc ** R.pts_to pos pc);
    let ld = !pld;
    let n = !pn;
    let pcur = !pos;
    let xe = WI.iterator_next_eos r ml_ops p_raw RW.jump_raw pmi pit it lr sh g;
    unfold (WI.iterator_next_eos_post r ml_ops p_raw pmi pit it lr xe);
    with pm_v y tl it' pm' . assert (
      WI.elt_or_serialized_match r ml_ops p_raw pm_v xe y **
      R.pts_to pit it' **
      WI.iterator_match r ml_ops p_raw pm' it' tl);
    let res = jit_elt r vf w pm_v xe #y out pos;
    Trade.elim_hyp_l (WI.elt_or_serialized_match r ml_ops p_raw pm_v xe y) (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr);
    Trade.trans (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l);
    WI.append_assoc_singleton #SB.bytes (Ghost.reveal ld) y tl;
    pn := ml_ops.sub n ml_ops.one;
    pld := Ghost.hide (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]);
    with v2 p2 . assert (pts_to out v2 ** R.pts_to pos p2);
    frame_trans (SZ.v p0) v (SZ.v pc) vc v2;
    if res {
      let pnew = !pos;
      let fl = SI.read_frame out pnew pcur;
      if (SZ.gt fl 0sz && SZ.eq fl (SZ.sub pcur pnew)) {
        assert (pure (W.r2l_post (id_enc y) (SZ.v pc) vc true (SZ.v p2) v2));
        assert (pure (Seq.slice v2 (SZ.v p2) (SZ.v pc) == Ghost.reveal y));
        assert (pure (L.fresh_frame pp y));
        SI.r2l_insert SI.lt_lex (SI.lt_lex_impl ()) out pnew pcur p0r;
        with v3 . assert (pts_to out v3);
        assert (pure (SI.r2l_mls_inv SI.lt_lex id_enc l (SZ.v p0) v (Ghost.reveal ld) true (SZ.v pc) vc));
        SI.r2l_mls_inv_step SI.lt_lex id_enc l (SZ.v p0) v (Ghost.reveal ld) y (SZ.v pc) vc (SZ.v p2) v2 v3;
        SI.sort_acc_snoc SI.lt_lex id_enc Seq.empty (Ghost.reveal ld) y;
        assert (pure (L.sf pp None (SI.sort_list SI.lt_lex id_enc (Ghost.reveal ld))));
        L.sf_ins pp None y (SI.sort_list SI.lt_lex id_enc (Ghost.reveal ld));
        assert (pure (L.sf pp None (SI.sort_list SI.lt_lex id_enc (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]))));
        assert (pure (SI.r2l_mls_inv SI.lt_lex id_enc l (SZ.v p0) v (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]) true (SZ.v p2) v3));
        assert (pure (jsml_inv pp l (SZ.v p0) v (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]) true (SZ.v p2) v3));
      } else {
        pok := false;
      }
    } else {
      pok := false;
    }
  };
  with it pmi lr . assert (R.pts_to pit it ** WI.iterator_match r ml_ops p_raw pmi it lr);
  with vc pc . assert (pts_to out vc ** R.pts_to pos pc);
  let ld = !pld;
  Trade.elim (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l);
  fold (raw_ml_sorted r pm x' x);
  let ok = !pok;
  if ok {
    List.Tot.append_l_nil (Ghost.reveal ld);
    let pend = !pos;
    if (ne && not (SZ.lt pend p0r)) {
      false
    } else {
      SI.r2l_mls_inv_end SI.lt_lex id_enc l (SZ.v p0) v (SZ.v pc) vc;
      L.acc_sized_set ne pp (SI.sort_list SI.lt_lex id_enc l);
      true
    }
  } else {
    false
  }
}

#pop-options

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

(* Terminals: check the raw input, then write it. Only the identifier,
   length and encoding of small integers, BOOLEAN and NULL are then
   correct by construction, so nothing is read back from the output. *)

#push-options "--fuel 2 --ifuel 1"
let acc_terminal_prefixed (id2: asn1_id_t) (k2: asn1_terminal_k) (b: SB.bytes)
: Lemma (requires (cacc id2 (ASN1_TERMINAL k2) b))
  (ensures (L.acc #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) b))
= ()

let acc_terminal_tlv (id: asn1_id_t) (k: asn1_terminal_k) (b: SB.bytes)
: Lemma (requires (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id #(ASN1_TERMINAL k) (asn1_terminal_as_parser k)) b))
  (ensures (cacc id (ASN1_TERMINAL k) b))
= ()
#pop-options

inline_for_extraction
fn jit_terminal_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (pm: perm)
  (w: jw (raw_terminal_rel id2 k2) (cacc id2 (ASN1_TERMINAL k2)) pm)
: jw #(asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2)) (cacc id (ASN1_TERMINAL (ASN1_PREFIXED_TERMINAL id2 k2))) pm
= (x': asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  terminal_prefixed_eq id id2 k2 pm x' x;
  let x2 = prefixed_down id2 k2 x';
  rewrite (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x' x) as (raw_tlv id (raw_terminal_rel id2 k2) pm x2 x);
  let res = jit_tlv id (raw_terminal_rel id2 k2) #(ASN1_TERMINAL (ASN1_PREFIXED_TERMINAL id2 k2)) (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) pm
    (jit_ext (raw_terminal_rel id2 k2) (raw_terminal_rel id2 k2) ()
      (cacc id2 (ASN1_TERMINAL k2)) (L.acc #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2))) (acc_terminal_prefixed id2 k2) pm w)
    x2 #x out pos;
  rewrite (raw_tlv id (raw_terminal_rel id2 k2) pm x2 x) as (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x' x);
  if res {
    acc_terminal_tlv id (ASN1_PREFIXED_TERMINAL id2 k2) x;
    true
  } else {
    false
  }
}

[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_leaf_tlv (id: asn1_id_t) (k: E.leaf_k) (u: squash (In.supported_terminal k)) (pm: perm)
: jw (raw_terminal_rel id k) (cacc id (ASN1_TERMINAL k)) pm
= terminal_leaf_equiv id k;
  jit_ext (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) ()
    (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id #(ASN1_TERMINAL k) (asn1_terminal_as_parser k))) (cacc id (ASN1_TERMINAL k)) (acc_terminal_tlv id k) pm
    (jit_tlv id (raw_leaf k) #(ASN1_TERMINAL k) (asn1_terminal_as_parser k) pm
      (jit_pre (raw_leaf k) (L.tacc k) (L.acc #asn1_weak_parser_kind (asn1_terminal_as_parser k)) (fun _ -> ()) pm
        (JT.pv k () pm) (RW.raw_write_leaf k pm)))

[@@In.asn1_pulse_attr]
let rec jit_write_terminal (id: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) (u: squash (In.supported_terminal k)) (pm: perm)
  (x': asn1_terminal_impl_t k) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jres (raw_terminal_rel id k) (cacc id (ASN1_TERMINAL k)) pm x' x out pos v p)
  (decreases k)
= [@inline_let] let vf : jw (raw_terminal_rel id k) (cacc id (ASN1_TERMINAL k)) pm =
  (match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    jit_terminal_prefixed id id2 k2 pm
      (fun x' #x out pos #v #p -> jit_write_terminal id2 k2 () pm x' #x out pos #v #p)
  | _ -> jit_leaf_tlv id k () pm)
  in vf x' #x out pos #v #p

[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_restricted_tlv (id: asn1_id_t) (k: E.leaf_k) (r: asn1_restriction k) (u: squash (In.supported_restriction k r)) (pm: perm)
: jw (raw_terminal_rel id k) (cacc id (ASN1_RESTRICTED_TERMINAL k r)) pm
= terminal_leaf_equiv id k;
  jit_ext (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) ()
    (cacc id (ASN1_RESTRICTED_TERMINAL k r)) (cacc id (ASN1_RESTRICTED_TERMINAL k r)) (fun _ -> ()) pm
    (jit_tlv id (raw_leaf k) #(ASN1_RESTRICTED_TERMINAL k r) (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) pm
      (jit_pre (raw_leaf k) (JT.pand (L.tacc k) (L.holds k (restriction_pred r)))
        (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r))) (fun w -> L.acc_restricted k r w) pm
        (JT.pc_then (raw_leaf k) JT.ptrue (L.tacc k) (L.tacc k) (L.holds k (restriction_pred r)) (fun _ -> ()) pm
          (JT.pv k () pm) (JT.pr k r () pm))
        (RW.raw_write_leaf k pm)))

(* DEFAULT of a PREFIXED terminal: validated locally, right after being
   written *)
[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_dec_local (#s: _) (#d: _) (dk: asn1_decorated_k s d) (u: squash (In.supported_dec dk /\ (ASN1_DEFAULT_TERMINAL? dk \/ ASN1_DEFAULT_RESTRICTED_TERMINAL? dk))) (pm: perm)
: jw (raw_dec_rel dk) (dacc dk) pm
= L.twins_of_single dk;
  jit_ext (raw_dec_rel dk) (raw_dec_rel dk) () (L.iacc (In.twins_of (PS.single dk))) (dacc dk) (fun _ -> ()) pm
    (jit_local (raw_dec_rel dk) pm
      (fun x' #x out pos #v #p -> RW.raw_write_dec dk pm x' #x out pos #v #p)
      (In.validate_seq (PS.single dk) (L.supported_single dk ()) None))

(* DEFAULT components: also check that the value is not the default one *)

[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_default (id0: asn1_id_t) (k: E.leaf_k) (defl: asn1_key_lit k) (u: squash (In.supported_default k)) (pm: perm)
: jw (raw_dec_rel (ASN1_DEFAULT_TERMINAL id0 #k defl)) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) pm
= let defv = key_of_lit k defl in
  dec_default_equiv id0 #k defl;
  terminal_leaf_equiv id0 k;
  L.iacc_default_none (ASN1_DEFAULT_TERMINAL id0 #k defl);
  jit_ext (raw_opt (raw_terminal_rel id0 k)) (raw_dec_rel (ASN1_DEFAULT_TERMINAL id0 #k defl)) ()
    (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) (fun _ -> ()) pm
    (jit_opt (raw_terminal_rel id0 k) (cacc id0 (Co.default_content k defv)) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) ()
      (L.iacc_default id0 #k defl) pm
      (jit_ext (raw_tlv id0 (raw_leaf k)) (raw_terminal_rel id0 k) ()
        (cacc id0 (Co.default_content k defv)) (cacc id0 (Co.default_content k defv)) (fun _ -> ()) pm
        (jit_tlv id0 (raw_leaf k) #(Co.default_content k defv) (asn1_content_as_parser (Co.default_content k defv)) pm
          (jit_pre (raw_leaf k) (JT.pand (L.tacc k) (L.holds k (defaultv_filter defv)))
            (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (Co.default_content k defv))) (fun w -> L.acc_default k defv w) pm
            (JT.pc_then (raw_leaf k) JT.ptrue (L.tacc k) (L.tacc k) (L.holds k (defaultv_filter defv)) (fun _ -> ()) pm
              (JT.pv k () pm) (JT.pn k defl () pm))
            (RW.raw_write_leaf k pm)))))

[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_default_restricted (id0: asn1_id_t) (k: E.leaf_k) (r: asn1_restriction k) (defl: asn1_key_lit k { restriction_pred r (key_of_lit k defl) })
  (u: squash (In.supported_default_restricted k r)) (pm: perm)
: jw (raw_dec_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) (dacc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) pm
= let defv = key_of_lit k defl in
  dec_default_restricted_equiv id0 #k r defl;
  terminal_leaf_equiv id0 k;
  L.iacc_default_none (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl);
  jit_ext (raw_opt (raw_terminal_rel id0 k)) (raw_dec_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) ()
    (dacc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) (dacc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) (fun _ -> ()) pm
    (jit_opt (raw_terminal_rel id0 k) (cacc id0 (Co.default_restricted_content k r defv)) (dacc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) ()
      (L.iacc_default_restricted id0 #k r defl) pm
      (jit_ext (raw_tlv id0 (raw_leaf k)) (raw_terminal_rel id0 k) ()
        (cacc id0 (Co.default_restricted_content k r defv)) (cacc id0 (Co.default_restricted_content k r defv)) (fun _ -> ()) pm
        (jit_tlv id0 (raw_leaf k) #(Co.default_restricted_content k r defv) (asn1_content_as_parser (Co.default_restricted_content k r defv)) pm
          (jit_pre (raw_leaf k) (JT.pand (JT.pand (L.tacc k) (L.holds k (restriction_pred r))) (L.holds k (defaultv_filter defv)))
            (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (Co.default_restricted_content k r defv))) (fun w -> L.acc_default_restricted k r defv w) pm
            (JT.pc_then (raw_leaf k) JT.ptrue (JT.pand (L.tacc k) (L.holds k (restriction_pred r))) (L.tacc k) (L.holds k (defaultv_filter defv)) (fun _ -> ()) pm
              (JT.pc_then (raw_leaf k) JT.ptrue (L.tacc k) (L.tacc k) (L.holds k (restriction_pred r)) (fun _ -> ()) pm
                (JT.pv k () pm) (JT.pr k r () pm))
              (JT.pn k defl () pm))
            (RW.raw_write_leaf k pm)))))

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
  | ASN1_SEQUENCE_OF ne k' ->
    content_seq_of_equiv id ne k';
    jit_ext (raw_tlv id (raw_ml (raw_rel k'))) (raw_content_rel id (ASN1_SEQUENCE_OF ne k')) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k')))) (cacc id k) (fun _ -> ()) pm
      (jit_tlv id (raw_ml (raw_rel k')) (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k')) pm
        (jit_ext (raw_ml (raw_rel k')) (raw_ml (raw_rel k')) ()
          (L.acc #asn1_weak_parser_kind (parse_sized_list ne (asn1_as_parser k'))) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k'))) (L.acc_seq_of ne k') pm
          (jit_write_ml (raw_rel k') ne (In.validate_k k' ()) (fun pm x' #x out pos #v #p -> jit_write_k k' () pm x' #x out pos #v #p) (share_k k') (gather_k k') pm)))
  | ASN1_SET_OF ne k' ->
    content_set_of_equiv id ne k';
    jit_ext (raw_tlv id (raw_ml_sorted (raw_rel k'))) (raw_content_rel id (ASN1_SET_OF ne k')) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_SET_OF ne k')))) (cacc id k) (fun _ -> ()) pm
      (jit_tlv id (raw_ml_sorted (raw_rel k')) (asn1_content_as_parser (ASN1_SET_OF ne k')) pm
        (jit_ext (raw_ml_sorted (raw_rel k')) (raw_ml_sorted (raw_rel k')) ()
          (L.acc #asn1_weak_parser_kind (parse_sized_set ne (asn1_as_parser k'))) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET_OF ne k'))) (L.acc_set_of ne k') pm
          (jit_write_ml_sorted (raw_rel k') ne (In.validate_k k' ()) (fun pm x' #x out pos #v #p -> jit_write_k k' () pm x' #x out pos #v #p) (share_k k') (gather_k k') pm)))
  | ASN1_SET ids items pf ->
    content_set_equiv id ids items pf;
    jit_ext (raw_tlv id (raw_items_rel true items)) (raw_content_rel id (ASN1_SET ids items pf)) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_SET ids items pf)))) (cacc id k) (fun _ -> ()) pm
      (jit_tlv id (raw_items_rel true items) (asn1_content_as_parser (ASN1_SET ids items pf)) pm
        (jit_ext (raw_items_rel true items) (raw_items_rel true items) ()
          (L.sacc (In.twins_of items)) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf))) (L.acc_set ids items pf) pm
          (fun x' #x out pos #v #p -> jit_write_set_items items () pm x' #x out pos #v #p)))
  | ASN1_TERMINAL k' ->
    content_terminal_equiv id k';
    jit_ext (raw_terminal_rel id k') (raw_content_rel id (ASN1_TERMINAL k')) ()
      (cacc id (ASN1_TERMINAL k')) (cacc id k) (fun _ -> ()) pm
      (fun x' #x out pos #v #p -> jit_write_terminal id k' () pm x' #x out pos #v #p)
  | ASN1_RESTRICTED_TERMINAL k' r ->
    content_restricted_equiv id k' r;
    jit_ext (raw_terminal_rel id k') (raw_content_rel id (ASN1_RESTRICTED_TERMINAL k' r)) ()
      (cacc id (ASN1_RESTRICTED_TERMINAL k' r)) (cacc id k) (fun _ -> ()) pm
      (jit_restricted_tlv id k' r () pm)
  | ASN1_ANY_DEFINED_BY idp prefix aid key_k ls ofb pf_wf pf_sup ->
    (* not supported by the raw writers *)
    content_adb_equiv id idp prefix aid key_k ls ofb pf_wf pf_sup;
    jit_ext (raw_false _) (raw_content_rel id k) () (cacc id k) (cacc id k) (fun _ -> ()) pm
      (jit_false _ (cacc id k) pm))
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

and jit_write_set_items (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (u: squash (In.supported_items ls /\ asn1_set_k_wf i)) (pm: perm)
  (x': asn1_items_impl_t ls) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jres (raw_items_rel true ls) (L.sacc (In.twins_of ls)) pm x' x out pos v p)
  (decreases ls)
= [@inline_let] let vf : jw (raw_items_rel true ls) (L.sacc (In.twins_of ls)) pm =
  (match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_nil_equiv true;
    jit_ext (raw_pure null_enc) (raw_items_rel true ASN1_GEN_ITEMS_NIL) ()
      (L.iacc []) (L.sacc (In.twins_of ls)) L.sacc_nil pm (jit_nil pm)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    items_single_equiv true dk;
    L.twins_of_single dk;
    L.set_cons_ok_intro dk ASN1_GEN_ITEMS_NIL;
    jit_ext (raw_dec_rel dk) (raw_items_rel true (PS.single dk)) ()
      (L.sacc1 (In.twin_of dk)) (L.sacc (In.twins_of ls)) (L.sacc_single (In.twin_of dk)) pm
      (jit_set_elt (In.twin_of dk) (In.has_id_dec dk ()) (raw_dec_rel dk) pm
        (fun x' #x out pos #v #p -> jit_write_dec dk () pm x' #x out pos #v #p))
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_cons_equiv true dk dk2 tl2;
    join_ins_equiv true (raw_dec_rel dk) (raw_items_rel true (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2));
    L.twins_of_cons2 dk dk2 tl2;
    L.set_cons_ok_intro dk (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2);
    jit_ext
      #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
      (raw_ins SI.lt_tag (raw_dec_rel dk) (raw_items_rel true (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
      (raw_items_rel true (PS.cons2 dk dk2 tl2)) ()
      (L.sacc (In.twin_of dk :: In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (L.sacc (In.twins_of ls)) (fun _ -> ()) pm
      (jit_set_cons (In.twin_of dk) (In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) ()
        (raw_dec_rel dk) (raw_items_rel true (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) pm
        (jit_set_elt (In.twin_of dk) (In.has_id_dec dk ()) (raw_dec_rel dk) pm
          (fun x' #x out pos #v #p -> jit_write_dec dk () pm x' #x out pos #v #p))
        (fun x' #x out pos #v #p -> jit_write_set_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) () pm x' #x out pos #v #p)))
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
  | ASN1_DEFAULT_TERMINAL id0 #k defl ->
    if ASN1_PREFIXED_TERMINAL? k
    then jit_dec_local dk () pm
    else jit_default id0 k defl () pm
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl ->
    jit_default_restricted id0 k r defl () pm
  | _ -> false_elim ())
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
      (jit_pre raw_slice (kacc k) (kacc k) (fun _ -> ()) pm
        (JT.pc_slice (In.validate_k ASN1_ANY_ILC ()) JT.ptrue (kacc k) (fun _ -> ()) pm)
        (RW.raw_write_slice pm)))
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
