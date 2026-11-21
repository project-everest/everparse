module ASN1.Pulse.JitWriter
#lang-pulse

(* Raw right-to-left writers with just-in-time checks.

   `jit_writer k` writes the bytes `w` of a raw Pulse representation `x`
   (`ASN1.Pulse.RawRel.raw_rel k pm x w`), like the raw writer
   `ASN1.Pulse.RawWriter.raw_write_k`, but it also checks that `w` is the
   DER encoding of a value of `k`: instead of validating the whole output
   after writing it, it checks each chunk while writing it:

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
   - ANY values are validated on the input slice, before being copied:
     each must be exactly one TLV;
   - ANY DEFINED BY: the prefix items and the payload are checked by
     their own JIT writers, and the fallback key by the terminal checks
     and, on the input value, by its disequality with each literal key;
     acceptance is proven structurally (`ASN1.Pulse.JitAdb`). A literal
     key is written as a constant;
   - DEFAULT components of PREFIXED type are compared with the DEFAULT
     value on the input (`ASN1.Pulse.DefaultEq`), then checked as
     terminals.

   So the writer makes one single pass: every check is on the input value,
   before writing it, and the output is never read back, except by the
   sorted insertion of SET and SET OF elements. `jit_writer` returns
   JIT_OK, JIT_NO_SPACE (the encoding does not fit) or JIT_INVALID.

   Internally, a JIT writer returns JIT_OK, JIT_NO_SPACE, JIT_INVALID or
   JIT_RETRY (rejected by a check stricter than DER); a writer of exactness
   `ex = true` (`jwg true`, `jwx`) never returns JIT_RETRY. Validity is
   compositional, so that a failed check yields JIT_INVALID (`jit_iff`),
   through terminals, RESTRICTED and DEFAULT terminals, TLVs (a content of
   2^32 bytes or more is also invalid), PREFIXED types, CHOICEs, SEQUENCEs
   and their components (each present component is one TLV with one of its
   own identifiers, and, by the well-formedness of the tags, the rest does
   not start with any of them: `ASN1.Pulse.JitFrame`,
   `ASN1.Pulse.JitWriter.SeqLemmas`), SET, SET OF, SEQUENCE OF, and ANY
   DEFINED BY (prefix items as SEQUENCE components, `ASN1.Pulse.JitAdbSeq`;
   literal alternatives, `ASN1.Pulse.JitAdbKey`).

   The only checks stricter than DER are about raw bytes that the schema
   cannot frame: an ANY slice must be exactly one TLV (an empty slice
   followed by a TLV, or two TLVs in one slice, might otherwise still
   parse), and the fallback of ANY DEFINED BY must not have the key of one
   of the literals (its payload might otherwise still parse as that
   literal alternative). Hence, at the top level, JIT_RETRY becomes
   JIT_INVALID, which means that the value has no valid encoding if the
   schema has neither ANY nor ANY DEFINED BY with a fallback (`ex_k`.) *)

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
module JA = ASN1.Pulse.JitAdb
module JK = ASN1.Pulse.JitAdbKey
module PA = ASN1.Pulse.ParseAdb
module ADB = ASN1.Pulse.AnyDefinedBy
module WA = ASN1.Pulse.WriteAdb
module JF = ASN1.Pulse.JitFrame
module SK = ASN1.Pulse.Sink
module DE = ASN1.Pulse.DefaultEq
module PSL = ASN1.Pulse.ParseSequence.Lemmas
module SL = ASN1.Pulse.JitWriter.SeqLemmas
module SetL = ASN1.Pulse.JitWriter.SetLemmas
module JAS = ASN1.Pulse.JitAdbSeq
module PSet = ASN1.Pulse.ParseSet.Lemmas
open Pulse.Lib.Trade

(* A JIT writer either writes `x` and checks that it satisfies `a`
   (JIT_OK), or fails, leaving the output after `p` untouched: JIT_NO_SPACE
   if `x` is too large, JIT_INVALID if `x` does not satisfy `a`, or
   JIT_RETRY if it could not tell (never for exact writers, `jwx`). *)

type jit_result =
| JIT_OK
| JIT_NO_SPACE
| JIT_INVALID
| JIT_RETRY

let jit_post (x: SB.bytes) (a: prop) (p: nat) (v: SB.bytes) (res: jit_result) (p': nat) (v': SB.bytes) : prop =
  Seq.length v' == Seq.length v /\
  p <= Seq.length v /\
  Seq.slice v' p (Seq.length v) == Seq.slice v p (Seq.length v) /\
  (res == JIT_OK ==> (W.r2l_post x p v true p' v' /\ a)) /\
  (res == JIT_NO_SPACE ==> Seq.length x > p) /\
  (res == JIT_INVALID ==> ~ a)

(* Keep JIT_NO_SPACE, turn any other failure into JIT_RETRY *)
inline_for_extraction
let ns_or_retry (r: jit_result) : jit_result =
  if JIT_NO_SPACE? r then JIT_NO_SPACE else JIT_RETRY

(* An exact (`ex == true`) JIT writer never returns JIT_RETRY *)
let jit_post_g (ex: bool) (x: SB.bytes) (a: prop) (p: nat) (v: SB.bytes) (res: jit_result) (p': nat) (v': SB.bytes) : prop =
  jit_post x a p v res p' v' /\ (ex == true ==> ~ (JIT_RETRY? res))

inline_for_extraction
let jwg (ex: bool) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) =
  (x': t) -> (#x: Ghost.erased SB.bytes) ->
  (out: SK.sink) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt jit_result
    (SK.sbuf out v ** pts_to pos p ** r pm x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . SK.sbuf out v' ** pts_to pos p' ** r pm x' x **
      pure (jit_post_g ex x (a x) (SZ.v p) v res (SZ.v p') v'))

inline_for_extraction
let jw (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) = jwg false r a pm

inline_for_extraction
let jwx (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) = jwg true r a pm

(* Change the exactness flag *)
inline_for_extraction
fn jit_cast (#ex1: bool) (ex2: bool) (sq: squash (ex2 == true ==> ex1 == true)) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) (w: jwg ex1 r a pm)
: jwg ex2 #t r a pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  w x' #x out pos
}

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
fn jit_ext (#ex: bool) (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2))
  (a1 a2: SB.bytes -> prop) (imp: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a2 x)))
  (pm: perm) (w: jwg ex r1 a1 pm)
: jw #t r2 a2 pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  rewrite (r2 pm x' x) as (r1 pm x' x);
  let res = w x' #x out pos;
  rewrite (r1 pm x' x) as (r2 pm x' x);
  if (JIT_OK? res) {
    imp x;
    JIT_OK
  } else {
    ns_or_retry res
  }
}

(* Same, when `a1` and `a2` are equivalent: also keeps JIT_INVALID *)
inline_for_extraction
fn jit_iff (#ex: bool) (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2))
  (a1 a2: SB.bytes -> prop) (imp: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a2 x)))
  (back: (x: SB.bytes) -> Lemma (requires (a2 x)) (ensures (a1 x)))
  (pm: perm) (w: jwg ex r1 a1 pm)
: jwg ex #t r2 a2 pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  rewrite (r2 pm x' x) as (r1 pm x' x);
  let res = w x' #x out pos;
  rewrite (r1 pm x' x) as (r2 pm x' x);
  if (JIT_OK? res) {
    imp x;
    JIT_OK
  } else {
    Classical.move_requires back x;
    res
  }
}

(* Forget exactness *)
inline_for_extraction
fn jit_weak (#ex: bool) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) (w: jwg ex r a pm)
: jw #t r a pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  w x' #x out pos
}

let sz_u32_fits (len: SZ.t)
: Lemma (SZ.fits (U32.v (SZ.sizet_to_uint32 len)))
= let n = SZ.v len in
  let m = U32.v (SZ.sizet_to_uint32 len) in
  if n < pow2 32 then FStar.Math.Lemmas.small_mod n (pow2 32);
  SZ.fits_lte m n

let tlv_overflow (len: SZ.t)
: Lemma (requires (~ (SZ.uint32_to_sizet (SZ.sizet_to_uint32 len) == len))) (ensures (SZ.v len >= 4294967296))
= assert_norm (pow2 32 == 4294967296)

inline_for_extraction
fn jit_tlv (#ex: bool) (id: asn1_id_t) (#t: Type0) (r: bprel t)
  (#ack: asn1_content_k) (pp: asn1_weak_parser (asn1_content_t ack))
  (pm: perm) (w: jwg ex r (L.acc #asn1_weak_parser_kind pp) pm)
: jwg ex #t (raw_tlv id r) (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id #ack pp)) pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_tlv id r pm x' x);
  with c . assert (r pm x' c);
  let p0 = !pos;
  let ok = w x' #c out pos;
  if (JIT_OK? ok) {
    with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
    let p1r = !pos;
    let len = SZ.sub p0 p1r;
    assert_norm (pow2 32 == 4294967296);
    sz_u32_fits len;
    if (SZ.eq (SZ.uint32_to_sizet (SZ.sizet_to_uint32 len)) len) {
      fold (W.vmatch_sz len (Seq.length c));
      let ok2 = SK.sw_hdr len #(Seq.length c) out pos;
      unfold (W.vmatch_sz len (Seq.length c));
      with v2 p2 . assert (SK.sbuf out v2 ** pts_to pos p2);
      frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
      if ok2 {
        let ok3 = SK.sw_id id out pos;
        with v3 p3 . assert (SK.sbuf out v3 ** pts_to pos p3);
        frame_trans (SZ.v p) v (SZ.v p2) v2 v3;
        fold (raw_tlv id r pm x' x);
        if ok3 {
          W.r2l_post_append (enc_hdr true (Seq.length c)) c (SZ.v p) v (SZ.v p1) v1 true (SZ.v p2) v2;
          W.r2l_post_append (asn1_id_enc id) (enc_hdr true (Seq.length c) `Seq.append` c) (SZ.v p) v (SZ.v p2) v2 true (SZ.v p3) v3;
          L.acc_tlv id #ack pp c;
          JIT_OK
        } else {
          JIT_NO_SPACE
        }
      } else {
        fold (raw_tlv id r pm x' x);
        JIT_NO_SPACE
      }
    } else {
      fold (raw_tlv id r pm x' x);
      tlv_overflow len;
      assert (pure (Seq.length c >= 4294967296));
      L.acc_tlv_iff id #ack pp c;
      JIT_INVALID
    }
  } else {
    fold (raw_tlv id r pm x' x);
    L.acc_tlv_iff id #ack pp c;
    ok
  }
}

(* Same, when `a1` and `a2` are equivalent on the nonempty encodings of
   present values *)
inline_for_extraction
fn jit_opt_ne (#t: Type0) (r: bprel t) (s: Ghost.erased (Set.set asn1_id_t)) (fr: JF.fr_t r s) (a1 a2: SB.bytes -> prop)
  (none: squash (a2 Seq.empty))
  (imp: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a2 x)))
  (back: (x: SB.bytes) -> Lemma (requires (a2 x /\ Seq.length x > 0)) (ensures (a1 x)))
  (#ex: bool) (pm: perm) (w: jwg ex r a1 pm)
: jwg ex #(option t) (raw_opt r) a2 pm
= (x': option t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (raw_opt r pm x' x) as (pure (Ghost.reveal x == Seq.empty));
      W.r2l_post_empty (SZ.v p) v;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt r pm x' x);
      JIT_OK
    }
    Some y -> {
      rewrite (raw_opt r pm x' x) as (r pm y x);
      fr pm y x;
      L.framed_ne s x;
      let res = w y #x out pos;
      rewrite (r pm y x) as (raw_opt r pm x' x);
      if (JIT_OK? res) {
        imp x;
        JIT_OK
      } else {
        Classical.move_requires back x;
        res
      }
    }
  }
}

(* An explicit default value: nothing is written *)
inline_for_extraction
fn jit_nd (d: SB.bytes) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (none: squash (a Seq.empty))
  (#ex: bool) (pm: perm) (dec: DE.dd r d pm) (w: jwg ex (raw_opt r) a pm)
: jwg ex #(option t) (raw_opt_nd d r) a pm
= (x': option t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (raw_opt_nd d r pm x' x) as (pure (Ghost.reveal x == Seq.empty));
      W.r2l_post_empty (SZ.v p) v;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt_nd d r pm x' x);
      JIT_OK
    }
    Some y -> {
      rewrite (raw_opt_nd d r pm x' x) as (raw_opt_nd d r pm (Some y) x);
      unfold (raw_opt_nd d r pm (Some y) x);
      with c . assert (r pm y c);
      let isd = dec y #c;
      if isd {
        W.r2l_post_empty (SZ.v p) v;
        fold (raw_opt_nd d r pm (Some y) x);
        rewrite (raw_opt_nd d r pm (Some y) x) as (raw_opt_nd d r pm x' x);
        JIT_OK
      } else {
        rewrite (r pm y c) as (raw_opt r pm (Some y) x);
        let res = w (Some y) #x out pos;
        rewrite (raw_opt r pm (Some y) x) as (r pm y c);
        fold (raw_opt_nd d r pm (Some y) x);
        rewrite (raw_opt_nd d r pm (Some y) x) as (raw_opt_nd d r pm x' x);
        res
      }
    }
  }
}

(* A non-exact variant of `jit_opt_ne` without framing: what is written
   is nonempty only if it is accepted (`ne`) *)
inline_for_extraction
fn jit_opt_a (#t: Type0) (r: bprel t) (a1 a2: SB.bytes -> prop)
  (none: squash (a2 Seq.empty))
  (imp: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a2 x)))
  (#ex: bool) (pm: perm) (w: jwg ex r a1 pm)
: jw #(option t) (raw_opt r) a2 pm
= (x': option t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (raw_opt r pm x' x) as (pure (Ghost.reveal x == Seq.empty));
      W.r2l_post_empty (SZ.v p) v;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt r pm x' x);
      JIT_OK
    }
    Some y -> {
      rewrite (raw_opt r pm x' x) as (r pm y x);
      let res = w y #x out pos;
      rewrite (r pm y x) as (raw_opt r pm x' x);
      if (JIT_OK? res) {
        imp x;
        JIT_OK
      } else {
        ns_or_retry res
      }
    }
  }
}

(* An explicit default value is omitted; any other value is written with
   `w`, whose acceptance `a1` implies `a2` for values other than the
   default *)
inline_for_extraction
fn jit_nd_ne (d: SB.bytes) (#t: Type0) (r: bprel t) (s: Ghost.erased (Set.set asn1_id_t)) (fr: JF.fr_t r s) (a1 a2: SB.bytes -> prop)
  (none: squash (a2 Seq.empty))
  (imp: (x: SB.bytes) -> Lemma (requires (a1 x /\ ~ (x == d))) (ensures (a2 x)))
  (back: (x: SB.bytes) -> Lemma (requires (a2 x /\ Seq.length x > 0)) (ensures (a1 x)))
  (pm: perm) (dec: DE.dd r d pm) (#ex: bool) (w: jwg ex r a1 pm)
: jwg ex #(option t) (raw_opt_nd d r) a2 pm
= (x': option t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (raw_opt_nd d r pm x' x) as (pure (Ghost.reveal x == Seq.empty));
      W.r2l_post_empty (SZ.v p) v;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt_nd d r pm x' x);
      JIT_OK
    }
    Some y -> {
      rewrite (raw_opt_nd d r pm x' x) as (raw_opt_nd d r pm (Some y) x);
      unfold (raw_opt_nd d r pm (Some y) x);
      with c . assert (r pm y c);
      let isd = dec y #c;
      if isd {
        W.r2l_post_empty (SZ.v p) v;
        fold (raw_opt_nd d r pm (Some y) x);
        rewrite (raw_opt_nd d r pm (Some y) x) as (raw_opt_nd d r pm x' x);
        JIT_OK
      } else {
        fr pm y c;
        L.framed_ne s c;
        let res = w y #c out pos;
        fold (raw_opt_nd d r pm (Some y) x);
        rewrite (raw_opt_nd d r pm (Some y) x) as (raw_opt_nd d r pm x' x);
        if (JIT_OK? res) {
          imp c;
          JIT_OK
        } else {
          Classical.move_requires back c;
          res
        }
      }
    }
  }
}

(* The length of the bytes of a raw slice *)
inline_for_extraction
fn raw_slice_len (pm: perm) (y: S.slice U8.t) (x: Ghost.erased SB.bytes)
requires raw_slice pm y x
returns n: SZ.t
ensures raw_slice pm y x ** pure (SZ.v n == Seq.length x)
{
  unfold (raw_slice pm y x);
  unfold (prel_slice_ser id_enc pm y x);
  S.pts_to_len y;
  fold (prel_slice_ser id_enc pm y x);
  fold (raw_slice pm y x);
  S.len y
}

(* Same as `jit_opt_ne`, for raw slices (ANY), which may be empty: then
   nothing needs to be written *)
inline_for_extraction
fn jit_opt_slice (a1 a2: SB.bytes -> prop)
  (none: squash (a2 Seq.empty))
  (imp: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a2 x)))
  (back: (x: SB.bytes) -> Lemma (requires (a2 x /\ Seq.length x > 0)) (ensures (a1 x)))
  (#ex: bool) (pm: perm) (w: jwg ex raw_slice a1 pm)
: jwg ex #(option (S.slice U8.t)) (raw_opt raw_slice) a2 pm
= (x': option (S.slice U8.t)) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (raw_opt raw_slice pm x' x) as (pure (Ghost.reveal x == Seq.empty));
      W.r2l_post_empty (SZ.v p) v;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt raw_slice pm x' x);
      JIT_OK
    }
    Some y -> {
      rewrite (raw_opt raw_slice pm x' x) as (raw_slice pm y x);
      let n = raw_slice_len pm y x;
      if (n = 0sz) {
        assert (pure (Seq.equal x Seq.empty));
        W.r2l_post_empty (SZ.v p) v;
        rewrite (raw_slice pm y x) as (raw_opt raw_slice pm x' x);
        JIT_OK
      } else {
        let res = w y #x out pos;
        rewrite (raw_slice pm y x) as (raw_opt raw_slice pm x' x);
        if (JIT_OK? res) {
          imp x;
          JIT_OK
        } else {
          Classical.move_requires back x;
          res
        }
      }
    }
  }
}

(* Same as `jit_iff`, when `a2` implies `a1` only on bytes framed by `s`,
   which the raw relation guarantees *)
inline_for_extraction
fn jit_iff_fr (#ex: bool) (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2))
  (s: FStar.Set.set asn1_id_t) (fr: JF.fr_t r1 s)
  (a1 a2: SB.bytes -> prop) (imp: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a2 x)))
  (back: (x: SB.bytes) -> Lemma (requires (a2 x /\ L.framed s x)) (ensures (a1 x)))
  (pm: perm) (w: jwg ex r1 a1 pm)
: jwg ex #t r2 a2 pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  rewrite (r2 pm x' x) as (r1 pm x' x);
  fr pm x' x;
  let res = w x' #x out pos;
  rewrite (r1 pm x' x) as (r2 pm x' x);
  if (JIT_OK? res) {
    imp x;
    JIT_OK
  } else {
    Classical.move_requires back x;
    res
  }
}

(* Exact alternative: each branch is framed, and `a` implies the
   acceptance of the branch on bytes framed like it *)
inline_for_extraction
fn jit_either_x (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (a1 a2 a: SB.bytes -> prop)
  (s1 s2: FStar.Set.set asn1_id_t) (fr1: JF.fr_t r1 s1) (fr2: JF.fr_t r2 s2)
  (imp1: (x: SB.bytes) -> Lemma (requires (a1 x)) (ensures (a x)))
  (imp2: (x: SB.bytes) -> Lemma (requires (a2 x)) (ensures (a x)))
  (back1: (x: SB.bytes) -> Lemma (requires (a x /\ L.framed s1 x)) (ensures (a1 x)))
  (back2: (x: SB.bytes) -> Lemma (requires (a x /\ L.framed s2 x)) (ensures (a2 x)))
  (#ex1 #ex2: bool) (pm: perm) (w1: jwg ex1 r1 a1 pm) (w2: jwg ex2 r2 a2 pm)
: jwg (ex1 && ex2) #(either t1 t2) (raw_either r1 r2) a pm
= (x': either t1 t2) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    Inl y -> {
      rewrite (raw_either r1 r2 pm x' x) as (r1 pm y x);
      fr1 pm y x;
      let res = w1 y #x out pos;
      rewrite (r1 pm y x) as (raw_either r1 r2 pm x' x);
      if (JIT_OK? res) {
        imp1 x;
        JIT_OK
      } else {
        Classical.move_requires back1 x;
        res
      }
    }
    Inr y -> {
      rewrite (raw_either r1 r2 pm x' x) as (r2 pm y x);
      fr2 pm y x;
      let res = w2 y #x out pos;
      rewrite (r2 pm y x) as (raw_either r1 r2 pm x' x);
      if (JIT_OK? res) {
        imp2 x;
        JIT_OK
      } else {
        Classical.move_requires back2 x;
        res
      }
    }
  }
}

inline_for_extraction
fn jit_false (t: Type0) (a: SB.bytes -> prop) (pm: perm)
: jwx #t (raw_false t) a pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_false t pm x' x);
  unreachable ()
}

inline_for_extraction
fn jit_nil (pm: perm)
: jwx #unit (raw_pure null_enc) (L.iacc []) pm
= (x': unit) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_pure null_enc pm x' x);
  fold (raw_pure null_enc pm x' x);
  W.r2l_post_empty (SZ.v p) v;
  L.iacc_nil ();
  JIT_OK
}

let cons_correct_wf (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin { Cons? tl })
  (c1 c2: SB.bytes) (p: nat) (v: SB.bytes) (p1: nat) (v1: SB.bytes) (p2: nat) (v2: SB.bytes)
: Lemma
  (requires (W.r2l_post c2 p v true p1 v1 /\ W.r2l_post c1 p1 v1 true p2 v2 /\
    L.iacc [hd] c1 /\ L.iacc tl c2 /\ SL.dfe hd c1 /\ SL.avoids (SL.hs hd) c2))
  (ensures (W.r2l_post (Seq.append c1 c2) p v true p2 v2 /\ L.iacc (hd :: tl) (Seq.append c1 c2)))
= W.r2l_post_append c1 c2 p v p1 v1 true p2 v2;
  let n = Seq.length v in
  Seq.slice_slice v1 p1 n 0 (p - p1);
  Seq.slice_slice v2 p1 n 0 (p - p1);
  SL.iacc_cons_wf hd tl v2 p2 p1 p

(* Exact SEQUENCE components, when the head `hd` is either one frame with
   one of its identifiers or an empty absent OPTIONAL/DEFAULT component
   (`fe`), and the tail does not start with any identifier of `hd` if `hd`
   is not PLAIN (`av`, from the well-formedness of the SEQUENCE). Then the
   SEQUENCE is valid iff both the head and the tail are, so no check is
   needed. *)
inline_for_extraction
fn jit_items_cons_x (#ex1 #ex2: bool) (hd: Ghost.erased gen_decorated_parser_twin) (tl: Ghost.erased (list gen_decorated_parser_twin) { Cons? tl })
  (shaped: squash (PSL.item_shaped hd))
  (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm)
  (fe: JF.fe_t r1 hd)
  (hs: Ghost.erased (Set.set asn1_id_t)) (sq: squash (Ghost.reveal hs == SL.hs hd))
  (av: JF.av_t r2 hs)
  (w1: jwg ex1 r1 (L.iacc [Ghost.reveal hd]) pm) (w2: jwg ex2 r2 (L.iacc tl) pm)
: jwg (ex1 && ex2) #(t1 & t2) (raw_cat r1 r2) (L.iacc (Ghost.reveal hd :: Ghost.reveal tl)) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_cat r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  fe pm (fst x') c1;
  av pm (snd x') c2;
  Classical.move_requires (SL.iacc_cons_inv_wf hd tl c1) c2;
  let ok = w2 (snd x') #c2 out pos;
  if (JIT_OK? ok) {
    with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (SK.sbuf out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    fold (raw_cat r1 r2 pm x' x);
    if (JIT_OK? res) {
      cons_correct_wf hd tl c1 c2 (SZ.v p) v (SZ.v p1) v1 (SZ.v p2) v2;
      JIT_OK
    } else {
      res
    }
  } else {
    fold (raw_cat r1 r2 pm x' x);
    ok
  }
}

let dfa_t (hd: gen_decorated_parser_twin) =
  (x: SB.bytes) -> Lemma (requires (L.iacc [hd] x)) (ensures (SL.dfe hd x))

(* An ANY head: what it writes is one frame (or nothing, if OPTIONAL) only
   if it is accepted (`dfa`), so JIT_INVALID cannot be reported, but nothing
   needs to be read back *)
inline_for_extraction
fn jit_items_cons_a (hd: Ghost.erased gen_decorated_parser_twin) (tl: Ghost.erased (list gen_decorated_parser_twin) { Cons? tl })
  (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm)
  (dfa: dfa_t hd)
  (hs: Ghost.erased (Set.set asn1_id_t)) (sq: squash (Ghost.reveal hs == SL.hs hd))
  (av: JF.av_t r2 hs)
  (#ex1 #ex2: bool) (w1: jwg ex1 r1 (L.iacc [Ghost.reveal hd]) pm) (w2: jwg ex2 r2 (L.iacc tl) pm)
: jw #(t1 & t2) (raw_cat r1 r2) (L.iacc (Ghost.reveal hd :: Ghost.reveal tl)) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_cat r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  av pm (snd x') c2;
  Seq.lemma_len_append c1 c2;
  let ok = w2 (snd x') #c2 out pos;
  if (JIT_OK? ok) {
    with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (SK.sbuf out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    fold (raw_cat r1 r2 pm x' x);
    if (JIT_OK? res) {
      dfa c1;
      cons_correct_wf hd tl c1 c2 (SZ.v p) v (SZ.v p1) v1 (SZ.v p2) v2;
      JIT_OK
    } else {
      ns_or_retry res
    }
  } else {
    fold (raw_cat r1 r2 pm x' x);
    ns_or_retry ok
  }
}

(* SET components: each component is written and checked on its own: it
   must be either empty (an absent OPTIONAL or DEFAULT component) or exactly
   one frame whose identifier is one of those of the component; then it is
   inserted at its sorted position into the components written so far. The
   disjointness of the tags of the components (`asn1_set_k_wf`) then
   ensures that the result is strictly sorted, each component appearing at
   most once. *)

(* Writers of SET components also report, when JIT_INVALID, that what
   they would have written is a sequence of TLVs with the identifiers of the
   components (`SetL.frs`), so that JIT_INVALID can be propagated through
   the insertion of the other components *)

let jit_post_s (its: list gen_decorated_parser_twin) (x: SB.bytes) (p: nat) (v: SB.bytes) (res: jit_result) (p': nat) (v': SB.bytes) : prop =
  jit_post x (L.sacc its x) p v res p' v' /\ (JIT_INVALID? res ==> SetL.frs (PSet.items_set its) x)

let jit_post_sg (ex: bool) (its: list gen_decorated_parser_twin) (x: SB.bytes) (p: nat) (v: SB.bytes) (res: jit_result) (p': nat) (v': SB.bytes) : prop =
  jit_post_s its x p v res p' v' /\ (ex == true ==> ~ (JIT_RETRY? res))

inline_for_extraction
let jwsg (ex: bool) (#t: Type0) (r: bprel t) (its: list gen_decorated_parser_twin) (pm: perm) =
  (x': t) -> (#x: Ghost.erased SB.bytes) ->
  (out: SK.sink) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt jit_result
    (SK.sbuf out v ** pts_to pos p ** r pm x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . SK.sbuf out v' ** pts_to pos p' ** r pm x' x **
      pure (jit_post_sg ex its x (SZ.v p) v res (SZ.v p') v'))

inline_for_extraction
let jws (#t: Type0) (r: bprel t) (its: list gen_decorated_parser_twin) (pm: perm) = jwsg false r its pm

(* No component *)
inline_for_extraction
fn jit_s_cast (#ex1: bool) (ex2: bool) (sq: squash (ex2 == true ==> ex1 == true)) (#t: Type0) (r: bprel t) (its: Ghost.erased (list gen_decorated_parser_twin)) (pm: perm) (w: jwsg ex1 r its pm)
: jwsg ex2 #t r its pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  w x' #x out pos
}

inline_for_extraction
fn jit_s_nil (pm: perm)
: jwsg true #unit (raw_pure null_enc) [] pm
= (x': unit) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_pure null_enc pm x' x);
  fold (raw_pure null_enc pm x' x);
  W.r2l_post_empty (SZ.v p) v;
  L.iacc_nil ();
  L.sacc_nil x;
  JIT_OK
}

(* Turn JIT_INVALID into JIT_RETRY *)
inline_for_extraction
fn jit_s_of_w (#t: Type0) (r: bprel t) (its: Ghost.erased (list gen_decorated_parser_twin)) (pm: perm) (w: jw r (L.sacc its) pm)
: jws #t r its pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let res = w x' #x out pos;
  if (JIT_INVALID? res) { JIT_RETRY } else { res }
}

inline_for_extraction
fn jit_w_of_s (#ex: bool) (#t: Type0) (r: bprel t) (its: Ghost.erased (list gen_decorated_parser_twin)) (pm: perm) (w: jwsg ex r its pm)
: jwg ex #t r (L.sacc its) pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  w x' #x out pos
}

inline_for_extraction
fn jit_s_ext (#ex: bool) (#t: Type0) (r1 r2: bprel t) (its1 its2: Ghost.erased (list gen_decorated_parser_twin))
  (sq: squash (prel_equiv r1 r2 /\ Ghost.reveal its1 == Ghost.reveal its2)) (pm: perm) (w: jwsg ex r1 its1 pm)
: jwsg ex #t r2 its2 pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  rewrite (r2 pm x' x) as (r1 pm x' x);
  let res = w x' #x out pos;
  rewrite (r1 pm x' x) as (r2 pm x' x);
  res
}

(* An ANY component: what it writes is either empty or one TLV only if it
   is accepted (`dfa`, from `JF.dfe_any`), so JIT_INVALID cannot be
   reported, but nothing needs to be read back *)

inline_for_extraction
fn jit_set_elt_a (hd: Ghost.erased gen_decorated_parser_twin) (shaped: squash (PSL.item_shaped hd)) (dfa: dfa_t hd)
  (#ex: bool) (#t: Type0) (r: bprel t) (pm: perm) (w: jwg ex r (L.iacc [Ghost.reveal hd]) pm)
: jw #t r (L.sacc1 hd) pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let res = w x' #x out pos;
  if (JIT_OK? res) {
    dfa x;
    SetL.elt_of_iacc hd x;
    JIT_OK
  } else {
    ns_or_retry res
  }
}

inline_for_extraction
fn jit_set_cons (hd: Ghost.erased gen_decorated_parser_twin) (tl: Ghost.erased (list gen_decorated_parser_twin))
  (sq: squash (L.set_cons_ok hd tl))
  (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm)
  (w1: jw r1 (L.sacc1 hd) pm) (#ex2: bool) (w2: jwsg ex2 r2 tl pm)
: jws #(t1 & t2) (raw_ins SI.lt_tag r1 r2) (Ghost.reveal hd :: Ghost.reveal tl) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_ins SI.lt_tag r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  let p0 = !pos;
  let ok = w2 (snd x') #c2 out pos;
  if (JIT_OK? ok) {
    with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
    let p1r = !pos;
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (SK.sbuf out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    if (JIT_OK? res) {
      let p2r = !pos;
      SK.sk_insert SI.lt_tag (SI.lt_tag_impl ()) out p2r p1r p0;
      with v3 . assert (SK.sbuf out v3);
      SI.r2l_post_ins SI.lt_tag c1 c2 (SZ.v p) v (SZ.v p1) v1 (SZ.v p2) v2 v3;
      L.sacc_cons hd tl c1 c2;
      fold (raw_ins SI.lt_tag r1 r2 pm x' x);
      JIT_OK
    } else {
      SI.ins_length SI.lt_tag c1 c2;
      fold (raw_ins SI.lt_tag r1 r2 pm x' x);
      ns_or_retry res
    }
  } else {
    SI.ins_length SI.lt_tag c1 c2;
    fold (raw_ins SI.lt_tag r1 r2 pm x' x);
    ns_or_retry ok
  }
}

(* A component other than ANY: what its writer writes is either empty or
   one TLV with one of its identifiers (`JF.fe_t`), so no runtime check is
   needed, and JIT_INVALID can be reported *)

inline_for_extraction
fn jit_set_single_x (hd: Ghost.erased gen_decorated_parser_twin)
  (sq: squash (L.set_cons_ok hd [] /\ PSL.item_shaped hd))
  (#t: Type0) (r: bprel t) (pm: perm) (fe: JF.fe_t r hd) (#ex: bool) (w: jwg ex r (L.iacc [Ghost.reveal hd]) pm)
: jwsg ex #t r [Ghost.reveal hd] pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  fe pm x' x;
  SetL.dfe_piece hd x;
  let res = w x' #x out pos;
  if (JIT_OK? res) {
    SetL.elt_of_iacc hd x;
    L.sacc_single hd x;
    JIT_OK
  } else if (JIT_INVALID? res) {
    SetL.set_single_inv hd x;
    JIT_INVALID
  } else {
    res
  }
}

inline_for_extraction
fn jit_set_cons_x (hd: Ghost.erased gen_decorated_parser_twin) (tl: Ghost.erased (list gen_decorated_parser_twin))
  (sq: squash (L.set_cons_ok hd tl /\ PSL.item_shaped hd))
  (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm)
  (fe: JF.fe_t r1 hd) (#ex1: bool) (w1: jwg ex1 r1 (L.iacc [Ghost.reveal hd]) pm) (#ex2: bool) (w2: jwsg ex2 r2 tl pm)
: jwsg (ex1 && ex2) #(t1 & t2) (raw_ins SI.lt_tag r1 r2) (Ghost.reveal hd :: Ghost.reveal tl) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_ins SI.lt_tag r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  fe pm (fst x') c1;
  SetL.dfe_piece hd c1;
  SI.ins_length SI.lt_tag c1 c2;
  let p0 = !pos;
  let ok = w2 (snd x') #c2 out pos;
  if (JIT_OK? ok) {
    with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
    let p1r = !pos;
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (SK.sbuf out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    if (JIT_OK? res) {
      let p2r = !pos;
      SetL.elt_of_iacc hd c1;
      SK.sk_insert SI.lt_tag (SI.lt_tag_impl ()) out p2r p1r p0;
      with v3 . assert (SK.sbuf out v3);
      SI.r2l_post_ins SI.lt_tag c1 c2 (SZ.v p) v (SZ.v p1) v1 (SZ.v p2) v2 v3;
      L.sacc_cons hd tl c1 c2;
      fold (raw_ins SI.lt_tag r1 r2 pm x' x);
      JIT_OK
    } else if (JIT_INVALID? res) {
      SetL.set_cons_invalid1 hd tl c1 c2;
      fold (raw_ins SI.lt_tag r1 r2 pm x' x);
      JIT_INVALID
    } else {
      fold (raw_ins SI.lt_tag r1 r2 pm x' x);
      ns_or_retry res
    }
  } else if (JIT_INVALID? ok) {
    SetL.set_cons_invalid2 hd tl c1 c2;
    fold (raw_ins SI.lt_tag r1 r2 pm x' x);
    JIT_INVALID
  } else {
    fold (raw_ins SI.lt_tag r1 r2 pm x' x);
    ns_or_retry ok
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
  (imp: (x: SB.bytes) -> Lemma (a x <==> a' x))
  (pm: perm) (c: JT.pcg r JT.ptrue a pm) (w: SK.srw r pm)
: jwx #t r a' pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let ok = c x' #x;
  if ok {
    imp x;
    let res = w x' #x out pos;
    if res { JIT_OK } else { JIT_NO_SPACE }
  } else {
    imp x;
    JIT_INVALID
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

inline_for_extraction
fn dw_ser (pm: perm)
: SK.drw #(S.slice U8.t) ser_rel pm
= (x': S.slice U8.t) (#x: Ghost.erased SB.bytes) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
{
  unfold (ser_rel pm x' x);
  unfold (PB.pts_to_parsed p_raw x' #pm x);
  with wb . assert (S.pts_to x' #pm wb);
  p_raw_consumed wb x;
  S.pts_to_len x';
  fold (PB.pts_to_parsed p_raw x' #pm x);
  fold (ser_rel pm x' x);
  SK.dry_sub (S.len x') x pos
}

inline_for_extraction
let sw_ser (pm: perm) : SK.srw ser_rel pm =
  SK.sw_of (raw_write_ser pm) (dw_ser pm)

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
  JT.valid_iff pp wb off1 valid;
  (valid && (off1 = S.len pl))
}

inline_for_extraction
fn jit_elt (#ex: bool) (#t: Type0) (r: bprel t)
  (#tp: Type0) (#pp: asn1_strong_parser tp) (vf: LPS.validator #tp #asn1_strong_parser_kind pp)
  (w: (pm: perm) -> jwg ex r (L.acc #asn1_strong_parser_kind pp) pm)
  (pm: perm)
: jwg ex #(WI.elt_or_serialized t) (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw) (L.acc #asn1_strong_parser_kind pp) pm
= (x': WI.elt_or_serialized t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
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
      let res = jit_pre ser_rel (L.acc #asn1_strong_parser_kind pp) (L.acc #asn1_strong_parser_kind pp) (fun _ -> ()) pm (pc_ser #tp #asn1_strong_parser_kind #pp vf pm) (sw_ser pm) pl #x out pos;
      rewrite (ser_rel pm pl x) as (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm x' x);
      res
    }
  }
}

(* The raw bytes of an element are one TLV (`L.tlvish`) *)
let tf_t (#t: Type0) (r: bprel t) =
  (pm: perm) -> (y: t) -> (x: Ghost.erased SB.bytes) ->
  stt_ghost unit emp_inames (r pm y x) (fun _ -> r pm y x ** pure (L.tlvish x))

ghost
fn tf_of_fr (#t: Type0) (r: bprel t) (s: FStar.Set.set asn1_id_t) (f: JF.fr_t r s) (pm: perm) (y: t) (x: Ghost.erased SB.bytes)
requires r pm y x
ensures r pm y x ** pure (L.tlvish x)
{
  f pm y x;
  L.framed_tlvish s x;
}

ghost
fn eos_tlvish (#t: Type0) (r: bprel t) (ex: bool) (tf: squash (ex == true) -> tf_t r) (pm: perm) (xe: WI.elt_or_serialized t) (y: Ghost.erased SB.bytes)
requires WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm xe y
ensures WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm xe y ** pure (ex == true ==> L.tlvish y)
{
  match xe {
    WI.EElement e -> {
      rewrite (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm xe y) as (r pm e y);
      if ex {
        tf () pm e y;
      };
      rewrite (r pm e y) as (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm xe y);
    }
    WI.ESerialized pl -> {
      rewrite (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm xe y) as (PB.pts_to_parsed p_raw pl #pm y);
      unfold (PB.pts_to_parsed p_raw pl #pm y);
      with wb . assert (S.pts_to pl #pm wb);
      L.p_raw_tlvish wb y;
      fold (PB.pts_to_parsed p_raw pl #pm y);
      rewrite (PB.pts_to_parsed p_raw pl #pm y) as (WI.elt_or_serialized_match r ml_ops #asn1_strong_parser_kind p_raw pm xe y);
    }
  }
}

let jml_frame (p0: nat) (v0 vc: SB.bytes) : prop =
  Seq.length vc == Seq.length v0 /\ p0 <= Seq.length v0 /\
  Seq.slice vc p0 (Seq.length v0) == Seq.slice v0 p0 (Seq.length v0)

let jml_inv (ex: bool) (#tp: Type) (pp: asn1_strong_parser tp) (l: list SB.bytes) (p0: nat) (v0: SB.bytes) (ld: list SB.bytes) (ok: jit_result) (pc: nat) (vc: SB.bytes) : prop =
  jml_frame p0 v0 vc /\
  (ok == JIT_OK ==> (WI.r2l_ml_inv id_enc l p0 v0 ld true pc vc /\ L.all_eacc pp ld)) /\
  (ok == JIT_NO_SPACE ==> Seq.length (W.enc_list id_enc l) > p0) /\
  (ok == JIT_INVALID ==> None? (SB.parse (parse_list pp) (W.enc_list id_enc l))) /\
  (ok == JIT_RETRY ==> ex == false)

let all_tlvish_snoc_if (ex: bool) (l: list SB.bytes) (y: SB.bytes)
: Lemma (requires (ex == true ==> (L.all_tlvish l /\ L.tlvish y))) (ensures (ex == true ==> L.all_tlvish (List.Tot.append l [y])))
= if ex then L.all_tlvish_snoc l y

let jsml_inv (ex: bool) (#tp: Type) (pp: asn1_strong_parser tp) (l: list SB.bytes) (p0: nat) (v0: SB.bytes) (ld: list SB.bytes) (ok: jit_result) (pc: nat) (vc: SB.bytes) : prop =
  jml_frame p0 v0 vc /\
  (ex == true ==> L.all_tlvish ld) /\
  (ok == JIT_OK ==> (SI.r2l_mls_inv SI.lt_lex id_enc l p0 v0 ld true pc vc /\ L.sf pp None (SI.sort_list SI.lt_lex id_enc ld))) /\
  (ok == JIT_NO_SPACE ==> Seq.length (W.enc_list id_enc l) > p0) /\
  (ok == JIT_INVALID ==> (ex == true /\ L.has_bad pp ld)) /\
  (ok == JIT_RETRY ==> ex == false)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 1"

inline_for_extraction
fn jit_write_ml (ex: bool) (#t: Type0) (r: bprel t) (ne: bool)
  (#tp: Type0) (#pp: asn1_strong_parser tp) (vf: LPS.validator #tp #asn1_strong_parser_kind pp)
  (shp: squash (L.tlv_shaped pp)) (tf: squash (ex == true) -> tf_t r)
  (w: (pm: perm) -> jwg ex r (L.acc #asn1_strong_parser_kind pp) pm)
  (sh: share_t r) (g: gather_t r) (pm: perm)
: jwg ex #(ml t) (raw_ml r) (L.acc #asn1_weak_parser_kind (parse_sized_list ne pp)) pm
= (x': ml t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p0: Ghost.erased SZ.t)
{
  unfold (raw_ml r pm x' x);
  with l . assert (WI.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw pm x' l);
  WI.mixed_list_match_length r ml_ops p_raw pm x' l;
  let n0 = LowParse.PulseParse.Iterator.Type.mixed_list_length ml_ops x';
  let it0 = WI.iterator_start r ml_ops p_raw RW.jump_raw pm x' l sh g;
  with pm0 . assert (WI.iterator_match r ml_ops p_raw pm0 it0 l);
  let mut pit = it0;
  let mut pn = n0;
  let mut pok = JIT_OK;
  WI.r2l_ml_inv_init id_enc l (SZ.v p0) v;
  let p0r = !pos;
  let mut pld : Ghost.erased (list SB.bytes) = Ghost.hide [];
  while (
    let ok = !pok;
    let n = !pn;
    (JIT_OK? ok && not (ml_ops.eq n ml_ops.zero))
  ) invariant exists* (it: LowParse.PulseParse.Iterator.Type.iterator SZ.t t) (pmi: perm) (ld: Ghost.erased (list SB.bytes)) (lr: list SB.bytes) (n: SZ.t) (ok: jit_result) (vc: SB.bytes) (pc: SZ.t) .
    R.pts_to pit it ** R.pts_to pld ld **
    WI.iterator_match r ml_ops p_raw pmi it lr **
    trade (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l) **
    R.pts_to pn n ** R.pts_to pok ok **
    SK.sbuf out vc ** R.pts_to pos pc **
    pure (
      Ghost.reveal l == List.Tot.append (Ghost.reveal ld) lr /\
      ml_ops.v n == List.Tot.length lr /\
      SZ.v p0r == SZ.v p0 /\
      jml_inv ex pp l (SZ.v p0) v (Ghost.reveal ld) ok (SZ.v pc) vc
    )
  decreases %[(if JIT_OK? (!pok) then 1 else 0); ml_ops.v (!pn)]
  {
    with it pmi lr . assert (R.pts_to pit it ** WI.iterator_match r ml_ops p_raw pmi it lr);
    with vc pc . assert (SK.sbuf out vc ** R.pts_to pos pc);
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
    eos_tlvish r ex tf pm_v xe y;
    Trade.elim_hyp_l (WI.elt_or_serialized_match r ml_ops p_raw pm_v xe y) (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr);
    Trade.trans (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l);
    WI.append_assoc_singleton #SB.bytes (Ghost.reveal ld) y tl;
    pn := ml_ops.sub n ml_ops.one;
    pld := Ghost.hide (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]);
    with v2 p2 . assert (SK.sbuf out v2 ** R.pts_to pos p2);
    frame_trans (SZ.v p0) v (SZ.v pc) vc v2;
    if (JIT_OK? res) {
      let pnew = !pos;
      if (SZ.lt pnew pcur) {
        SK.sk_reverse_range out pnew pcur;
        with v3 . assert (SK.sbuf out v3);
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
        assert (pure (jml_inv ex pp l (SZ.v p0) v (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]) JIT_OK (SZ.v p2) v3));
      } else {
        (* unreachable: accepted elements are nonempty *)
        L.acc_tlv_ne pp y;
        pok := JIT_RETRY;
      }
    } else if (JIT_NO_SPACE? res) {
      WI.r2l_ml_inv_fail id_enc l (SZ.v p0) v (Ghost.reveal ld) y tl (SZ.v pc) vc (SZ.v p2) v2;
      pok := JIT_NO_SPACE;
    } else if (ex && JIT_INVALID? res) {
      L.list_invalid pp (Ghost.reveal ld) y tl;
      pok := JIT_INVALID;
    } else {
      pok := JIT_RETRY;
    }
  };
  with it pmi lr . assert (R.pts_to pit it ** WI.iterator_match r ml_ops p_raw pmi it lr);
  with vc pc . assert (SK.sbuf out vc ** R.pts_to pos pc);
  let ld = !pld;
  Trade.elim (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l);
  fold (raw_ml r pm x' x);
  let ok = !pok;
  if (JIT_OK? ok) {
    List.Tot.append_l_nil (Ghost.reveal ld);
    let pend = !pos;
    if (ne && not (SZ.lt pend p0r)) {
      L.sized_list_empty pp (W.enc_list id_enc l);
      JIT_INVALID
    } else {
      SK.sk_reverse_range out pend p0r;
      with v3 . assert (SK.sbuf out v3);
      WI.r2l_ml_inv_end id_enc l (SZ.v p0) v (SZ.v pc) vc v3;
      L.acc_sized_list ne pp l;
      JIT_OK
    }
  } else if (JIT_INVALID? ok) {
    L.sized_list_none ne pp (W.enc_list id_enc l);
    JIT_INVALID
  } else {
    ok
  }
}

(* Since the elements are each one TLV, an accepted element is one
   frame, so that it can be inserted without further check. If an
   element is rejected, then the remaining elements are only read (not
   written), to show that they are each one TLV, so that the sorted
   concatenation is rejected as well. *)
inline_for_extraction
fn jit_write_ml_sorted (ex: bool) (#t: Type0) (r: bprel t) (ne: bool)
  (#tp: Type0) (#pp: asn1_strong_parser tp) (vf: LPS.validator #tp #asn1_strong_parser_kind pp)
  (shp: squash (L.tlv_shaped pp)) (tf: squash (ex == true) -> tf_t r)
  (w: (pm: perm) -> jwg ex r (L.acc #asn1_strong_parser_kind pp) pm)
  (sh: share_t r) (g: gather_t r) (pm: perm)
: jwg ex #(ml t) (raw_ml_sorted r) (L.acc #asn1_weak_parser_kind (parse_sized_set ne pp)) pm
= (x': ml t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p0: Ghost.erased SZ.t)
{
  unfold (raw_ml_sorted r pm x' x);
  with l . assert (WI.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw pm x' l);
  WI.mixed_list_match_length r ml_ops p_raw pm x' l;
  let n0 = LowParse.PulseParse.Iterator.Type.mixed_list_length ml_ops x';
  let it0 = WI.iterator_start r ml_ops p_raw RW.jump_raw pm x' l sh g;
  with pm0 . assert (WI.iterator_match r ml_ops p_raw pm0 it0 l);
  let mut pit = it0;
  let mut pn = n0;
  let mut pok = JIT_OK;
  SI.r2l_mls_inv_init SI.lt_lex id_enc l (SZ.v p0) v;
  L.sf_empty pp;
  let p0r = !pos;
  let mut pld : Ghost.erased (list SB.bytes) = Ghost.hide [];
  while (
    let ok = !pok;
    let n = !pn;
    ((JIT_OK? ok || JIT_INVALID? ok) && not (ml_ops.eq n ml_ops.zero))
  ) invariant exists* (it: LowParse.PulseParse.Iterator.Type.iterator SZ.t t) (pmi: perm) (ld: Ghost.erased (list SB.bytes)) (lr: list SB.bytes) (n: SZ.t) (ok: jit_result) (vc: SB.bytes) (pc: SZ.t) .
    R.pts_to pit it ** R.pts_to pld ld **
    WI.iterator_match r ml_ops p_raw pmi it lr **
    trade (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l) **
    R.pts_to pn n ** R.pts_to pok ok **
    SK.sbuf out vc ** R.pts_to pos pc **
    pure (
      Ghost.reveal l == List.Tot.append (Ghost.reveal ld) lr /\
      ml_ops.v n == List.Tot.length lr /\
      SZ.v p0r == SZ.v p0 /\
      jsml_inv ex pp l (SZ.v p0) v (Ghost.reveal ld) ok (SZ.v pc) vc
    )
  decreases %[(if (JIT_OK? (!pok) || JIT_INVALID? (!pok)) then 1 else 0); ml_ops.v (!pn)]
  {
    with it pmi lr . assert (R.pts_to pit it ** WI.iterator_match r ml_ops p_raw pmi it lr);
    with vc pc . assert (SK.sbuf out vc ** R.pts_to pos pc);
    let ld = !pld;
    let n = !pn;
    let ok = !pok;
    let pcur = !pos;
    let xe = WI.iterator_next_eos r ml_ops p_raw RW.jump_raw pmi pit it lr sh g;
    unfold (WI.iterator_next_eos_post r ml_ops p_raw pmi pit it lr xe);
    with pm_v y tl it' pm' . assert (
      WI.elt_or_serialized_match r ml_ops p_raw pm_v xe y **
      R.pts_to pit it' **
      WI.iterator_match r ml_ops p_raw pm' it' tl);
    eos_tlvish r ex tf pm_v xe y;
    if (JIT_INVALID? ok) {
      (* only read the remaining elements *)
      Trade.elim_hyp_l (WI.elt_or_serialized_match r ml_ops p_raw pm_v xe y) (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr);
      Trade.trans (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l);
      WI.append_assoc_singleton #SB.bytes (Ghost.reveal ld) y tl;
      pn := ml_ops.sub n ml_ops.one;
      pld := Ghost.hide (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]);
      assert (pure (ex == true));
      assert (pure (L.tlvish y));
      L.all_tlvish_snoc (Ghost.reveal ld) y;
      L.has_bad_snoc pp (Ghost.reveal ld) y;
      assert (pure (L.has_bad pp (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y])));
    } else {
    let res = jit_elt r vf w pm_v xe #y out pos;
    Trade.elim_hyp_l (WI.elt_or_serialized_match r ml_ops p_raw pm_v xe y) (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr);
    Trade.trans (WI.iterator_match r ml_ops p_raw pm' it' tl) (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l);
    WI.append_assoc_singleton #SB.bytes (Ghost.reveal ld) y tl;
    pn := ml_ops.sub n ml_ops.one;
    pld := Ghost.hide (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]);
    all_tlvish_snoc_if ex (Ghost.reveal ld) y;
    L.has_bad_snoc pp (Ghost.reveal ld) y;
    with v2 p2 . assert (SK.sbuf out v2 ** R.pts_to pos p2);
    frame_trans (SZ.v p0) v (SZ.v pc) vc v2;
    if (JIT_OK? res) {
      let pnew = !pos;
      assert (pure (W.r2l_post (id_enc y) (SZ.v pc) vc true (SZ.v p2) v2));
      assert (pure (Seq.slice v2 (SZ.v p2) (SZ.v pc) == Ghost.reveal y));
      L.acc_frame pp y;
      assert (pure (L.fresh_frame pp y));
      SK.sk_insert SI.lt_lex (SI.lt_lex_impl ()) out pnew pcur p0r;
      with v3 . assert (SK.sbuf out v3);
      assert (pure (SI.r2l_mls_inv SI.lt_lex id_enc l (SZ.v p0) v (Ghost.reveal ld) true (SZ.v pc) vc));
      SI.r2l_mls_inv_step SI.lt_lex id_enc l (SZ.v p0) v (Ghost.reveal ld) y (SZ.v pc) vc (SZ.v p2) v2 v3;
      SI.sort_acc_snoc SI.lt_lex id_enc Seq.empty (Ghost.reveal ld) y;
      assert (pure (L.sf pp None (SI.sort_list SI.lt_lex id_enc (Ghost.reveal ld))));
      L.sf_ins pp None y (SI.sort_list SI.lt_lex id_enc (Ghost.reveal ld));
      assert (pure (L.sf pp None (SI.sort_list SI.lt_lex id_enc (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]))));
      assert (pure (SI.r2l_mls_inv SI.lt_lex id_enc l (SZ.v p0) v (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]) true (SZ.v p2) v3));
      assert (pure (jsml_inv ex pp l (SZ.v p0) v (List.Tot.append (Ghost.reveal ld) [Ghost.reveal y]) JIT_OK (SZ.v p2) v3));
    } else if (JIT_NO_SPACE? res) {
      SI.r2l_mls_inv_fail SI.lt_lex id_enc l (SZ.v p0) v (Ghost.reveal ld) y tl (SZ.v pc) vc (SZ.v p2) v2;
      pok := JIT_NO_SPACE;
    } else if (ex && JIT_INVALID? res) {
      pok := JIT_INVALID;
    } else {
      pok := JIT_RETRY;
    }
    }
  };
  with it pmi lr . assert (R.pts_to pit it ** WI.iterator_match r ml_ops p_raw pmi it lr);
  with vc pc . assert (SK.sbuf out vc ** R.pts_to pos pc);
  let ld = !pld;
  Trade.elim (WI.iterator_match r ml_ops p_raw pmi it lr) (WI.mixed_list_match r ml_ops p_raw pm x' l);
  fold (raw_ml_sorted r pm x' x);
  let ok = !pok;
  if (JIT_OK? ok) {
    List.Tot.append_l_nil (Ghost.reveal ld);
    let pend = !pos;
    if (ne && not (SZ.lt pend p0r)) {
      SI.r2l_mls_inv_end SI.lt_lex id_enc l (SZ.v p0) v (SZ.v pc) vc;
      L.set_empty pp (SI.sort_list SI.lt_lex id_enc l);
      JIT_INVALID
    } else {
      SI.r2l_mls_inv_end SI.lt_lex id_enc l (SZ.v p0) v (SZ.v pc) vc;
      L.acc_sized_set ne pp (SI.sort_list SI.lt_lex id_enc l);
      JIT_OK
    }
  } else if (JIT_INVALID? ok) {
    List.Tot.append_l_nil (Ghost.reveal ld);
    L.set_invalid ne pp (Ghost.reveal ld);
    JIT_INVALID
  } else {
    SI.sort_list_length SI.lt_lex id_enc l;
    ok
  }
}

#pop-options

(* ANY DEFINED BY: the prefix items are written and checked as in a
   SEQUENCE, and so is the payload; only the key is read back from the
   output, to check that it selects the payload that was written. *)

let aan (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
  (items: list gen_decorated_parser_twin) (w: SB.bytes) : prop =
  JA.aacc items (ADB.adb_sfx_none kid key_k ls) w

let aas (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (items: list gen_decorated_parser_twin) (w: SB.bytes) : prop =
  JA.aacc items (ADB.adb_sfx_some kid key_k ls fb) w

(* Exact prefix items, when the head is not ANY: from the well-formedness
   of the tags of the prefix items, as in `jit_items_cons_x` *)
let acons_correct_x (aa: list gen_decorated_parser_twin -> SB.bytes -> prop) (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin)
  (c1 c2: SB.bytes) (p: nat) (v: SB.bytes) (p1: nat) (v1: SB.bytes) (p2: nat) (v2: SB.bytes)
: Lemma
  (requires (JAS.acons_x_ok aa /\ W.r2l_post c2 p v true p1 v1 /\ W.r2l_post c1 p1 v1 true p2 v2 /\
    L.iacc [hd] c1 /\ aa tl c2 /\ SL.dfe hd c1 /\ SL.avoids (SL.hs hd) c2))
  (ensures (W.r2l_post (Seq.append c1 c2) p v true p2 v2 /\ aa (hd :: tl) (Seq.append c1 c2)))
= W.r2l_post_append c1 c2 p v p1 v1 true p2 v2;
  let n = Seq.length v in
  Seq.slice_slice v1 p1 n 0 (p - p1);
  Seq.slice_slice v2 p1 n 0 (p - p1);
  assert (JAS.acons_wf_at aa hd tl v2 p2 p1 p)

let aan_acons_x (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk))
: Lemma (JAS.acons_x_ok (aan kid key_k ls))
= JA.twin_ok_none kid key_k ls;
  JAS.aacc_acons_x (ADB.adb_sfx_none kid key_k ls) (aan kid key_k ls) (fun _ _ -> ())

let aas_acons_x (kid: asn1_id_t) (key_k: asn1_terminal_k) (ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
: Lemma (JAS.acons_x_ok (aas kid key_k ls fb))
= JA.twin_ok_some kid key_k ls fb;
  JAS.aacc_acons_x (ADB.adb_sfx_some kid key_k ls fb) (aas kid key_k ls fb) (fun _ _ -> ())

inline_for_extraction
fn jit_acons_x (#ex1 #ex2: bool) (hd: Ghost.erased gen_decorated_parser_twin) (tl: Ghost.erased (list gen_decorated_parser_twin))
  (shaped: squash (PSL.item_shaped hd))
  (aa: Ghost.erased (list gen_decorated_parser_twin -> SB.bytes -> prop)) (acx: squash (JAS.acons_x_ok aa))
  (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm)
  (fe: JF.fe_t r1 hd)
  (hs: Ghost.erased (Set.set asn1_id_t)) (sq: squash (Ghost.reveal hs == SL.hs hd))
  (av: JF.av_t r2 hs)
  (w1: jwg ex1 r1 (L.iacc [Ghost.reveal hd]) pm) (w2: jwg ex2 r2 (Ghost.reveal aa tl) pm)
: jwg (ex1 && ex2) #(t1 & t2) (raw_cat r1 r2) (Ghost.reveal aa (Ghost.reveal hd :: Ghost.reveal tl)) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_cat r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  fe pm (fst x') c1;
  av pm (snd x') c2;
  assert (pure (JAS.acons_inv_at aa hd tl c1 c2));
  let ok = w2 (snd x') #c2 out pos;
  if (JIT_OK? ok) {
    with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (SK.sbuf out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    fold (raw_cat r1 r2 pm x' x);
    if (JIT_OK? res) {
      acons_correct_x aa hd tl c1 c2 (SZ.v p) v (SZ.v p1) v1 (SZ.v p2) v2;
      JIT_OK
    } else {
      res
    }
  } else {
    fold (raw_cat r1 r2 pm x' x);
    ok
  }
}

(* An ANY prefix item: as `jit_acons_x`, with `dfa` instead of `fe` *)
inline_for_extraction
fn jit_acons_a (#ex1 #ex2: bool) (hd: Ghost.erased gen_decorated_parser_twin) (tl: Ghost.erased (list gen_decorated_parser_twin))
  (shaped: squash (PSL.item_shaped hd))
  (aa: Ghost.erased (list gen_decorated_parser_twin -> SB.bytes -> prop)) (acx: squash (JAS.acons_x_ok aa))
  (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm)
  (dfa: dfa_t hd)
  (hs: Ghost.erased (Set.set asn1_id_t)) (sq: squash (Ghost.reveal hs == SL.hs hd))
  (av: JF.av_t r2 hs)
  (w1: jwg ex1 r1 (L.iacc [Ghost.reveal hd]) pm) (w2: jwg ex2 r2 (Ghost.reveal aa tl) pm)
: jw #(t1 & t2) (raw_cat r1 r2) (Ghost.reveal aa (Ghost.reveal hd :: Ghost.reveal tl)) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_cat r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  av pm (snd x') c2;
  let ok = w2 (snd x') #c2 out pos;
  if (JIT_OK? ok) {
    with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (SK.sbuf out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    fold (raw_cat r1 r2 pm x' x);
    if (JIT_OK? res) {
      dfa c1;
      acons_correct_x aa hd tl c1 c2 (SZ.v p) v (SZ.v p1) v1 (SZ.v p2) v2;
      JIT_OK
    } else {
      ns_or_retry res
    }
  } else {
    fold (raw_cat r1 r2 pm x' x);
    ns_or_retry ok
  }
}

(* A literal key, then its payload: the payload is written and checked,
   then the key, as a TLV whose contents are those of the literal. The
   dispatch then selects exactly the payload of the literal, so nothing
   needs to be read back (`lem`, from `JK.lit_iff`). *)
inline_for_extraction
fn jit_lit (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k)
  (#t: Type0) (r: bprel t) (a b: SB.bytes -> prop)
  (lem: (c: SB.bytes) -> Lemma (a (Seq.append (WA.raw_key_enc kid key_k kx) c) <==> (Seq.length (JK.raw_key_c key_k kx) < 4294967296 /\ b c)))
  (pm: perm) (#ex: bool) (w: jwg ex r b pm)
: jwg ex #t (raw_pre (WA.raw_key_enc kid key_k kx) r) a pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_pre (WA.raw_key_enc kid key_k kx) r pm x' x);
  with c . assert (r pm x' c);
  JK.raw_key_enc_c kid key_k kx;
  lem c;
  let ok = w x' #c out pos;
  if (JIT_OK? ok) {
    with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
    let p1r = !pos;
    fold (prel_emp unit unit 1.0R () ());
    let ok2 = SK.sc_raw_key_c key_k kx () #() out pos;
    unfold (prel_emp unit unit 1.0R () ());
    with v2 p2 . assert (SK.sbuf out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    if ok2 {
      let p2r = !pos;
      let len = SZ.sub p1r p2r;
      assert_norm (pow2 32 == 4294967296);
      let len32 = SZ.sizet_to_uint32 len;
      sz_u32_fits len;
      if (SZ.eq (SZ.uint32_to_sizet len32) len) {
        fold (W.vmatch_sz len (Seq.length (JK.raw_key_c key_k kx)));
        let ok3 = SK.sw_hdr len #(Seq.length (JK.raw_key_c key_k kx)) out pos;
        unfold (W.vmatch_sz len (Seq.length (JK.raw_key_c key_k kx)));
        with v3 p3 . assert (SK.sbuf out v3 ** pts_to pos p3);
        frame_trans (SZ.v p) v (SZ.v p2) v2 v3;
        if ok3 {
          let ok4 = SK.sw_id kid out pos;
          with v4 p4 . assert (SK.sbuf out v4 ** pts_to pos p4);
          frame_trans (SZ.v p) v (SZ.v p3) v3 v4;
          fold (raw_pre (WA.raw_key_enc kid key_k kx) r pm x' x);
          if ok4 {
            W.r2l_post_append (enc_hdr true (Seq.length (JK.raw_key_c key_k kx))) (JK.raw_key_c key_k kx) (SZ.v p1) v1 (SZ.v p2) v2 true (SZ.v p3) v3;
            W.r2l_post_append (asn1_id_enc kid) (enc_hdr true (Seq.length (JK.raw_key_c key_k kx)) `Seq.append` JK.raw_key_c key_k kx) (SZ.v p1) v1 (SZ.v p3) v3 true (SZ.v p4) v4;
            W.r2l_post_append (WA.raw_key_enc kid key_k kx) c (SZ.v p) v (SZ.v p1) v1 true (SZ.v p4) v4;
            JIT_OK
          } else {
            JIT_NO_SPACE
          }
        } else {
          fold (raw_pre (WA.raw_key_enc kid key_k kx) r pm x' x);
          JIT_NO_SPACE
        }
      } else {
        fold (raw_pre (WA.raw_key_enc kid key_k kx) r pm x' x);
        tlv_overflow len;
        JIT_INVALID
      }
    } else {
      fold (raw_pre (WA.raw_key_enc kid key_k kx) r pm x' x);
      JIT_NO_SPACE
    }
  } else {
    fold (raw_pre (WA.raw_key_enc kid key_k kx) r pm x' x);
    ok
  }
}

(* Either branch, with the same acceptance *)
inline_for_extraction
fn jit_either_same (#ex: bool) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (a: SB.bytes -> prop)
  (pm: perm) (w1: jwg ex r1 a pm) (w2: jwg ex r2 a pm)
: jwg ex #(either t1 t2) (raw_either r1 r2) a pm
= (x': either t1 t2) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    Inl y -> {
      rewrite (raw_either r1 r2 pm x' x) as (r1 pm y x);
      let res = w1 y #x out pos;
      rewrite (r1 pm y x) as (raw_either r1 r2 pm x' x);
      res
    }
    Inr y -> {
      rewrite (raw_either r1 r2 pm x' x) as (r2 pm y x);
      let res = w2 y #x out pos;
      rewrite (r2 pm y x) as (raw_either r1 r2 pm x' x);
      res
    }
  }
}

(* The fallback: the key is none of the literals of the table `lsf` *)

let rec nl (kid: asn1_id_t) (key_k: asn1_terminal_k) (lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (w: SB.bytes) : Tot prop (decreases lsf) =
  match lsf with
  | [] -> True
  | (kx, _) :: tl -> JA.not_lit kid key_k (key_of_lit key_k kx) w /\ nl kid key_k tl w

#push-options "--fuel 1 --ifuel 1"
let app_nil_l (#a: Type) (l: list a)
: Lemma (List.Tot.append [] l == l)
= ()

let nl_cons_eq (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (w: SB.bytes)
: Lemma (nl kid key_k ((kx, y) :: tl) w <==> (JA.not_lit kid key_k (key_of_lit key_k kx) w /\ nl kid key_k tl w))
= ()

let rec nl_afb (kid: asn1_id_t) (key_k: asn1_terminal_k) (lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk) (w: SB.bytes)
: Lemma (requires (nl kid key_k lsf w /\ JA.fbacc kid key_k fb w)) (ensures (JA.afbacc kid key_k lsf fb w)) (decreases lsf)
= match lsf with
  | [] -> ()
  | (kx, y) :: tl ->
    nl_afb kid key_k tl fb w;
    JA.afbacc_skip kid key_k kx y tl fb w
#pop-options

(* The key of the input is none of the literals of `lsf` (checked on the
   input, before writing) *)
let rec nlc (kid: asn1_id_t) (key_k: asn1_terminal_k) (lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (c: SB.bytes) : Tot prop (decreases lsf) =
  match lsf with
  | [] -> True
  | (kx, _) :: tl -> ~ (c == WA.raw_key_enc kid key_k kx) /\ nlc kid key_k tl c

#push-options "--fuel 1 --ifuel 1"
let nlc_cons_eq (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (y: asn1_gen_items_lk) (tl: list (asn1_key_lit key_k & asn1_gen_items_lk)) (c: SB.bytes)
: Lemma (nlc kid key_k ((kx, y) :: tl) c <==> (~ (c == WA.raw_key_enc kid key_k kx) /\ nlc kid key_k tl c))
= ()

let rec nl_of_nlc (kid: asn1_id_t) (key_k: asn1_terminal_k) (lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (c1 c2: SB.bytes)
: Lemma
  (requires (In.adb_key_supported key_k /\
    L.acc #asn1_strong_parser_kind (parse_asn1_ILC kid (asn1_content_as_parser (ASN1_TERMINAL key_k))) c1 /\
    nlc kid key_k lsf c1))
  (ensures (nl kid key_k lsf (Seq.append c1 c2)))
  (decreases lsf)
= match lsf with
  | [] -> ()
  | (kx, _) :: tl ->
    JK.not_lit_of_ne kid key_k kx c1 c2;
    nl_of_nlc kid key_k tl c1 c2
#pop-options

inline_for_extraction
let nl_t (kid: asn1_id_t) (key_k: asn1_terminal_k) (lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (pm: perm) =
  (x': asn1_terminal_impl_t key_k) -> (#c: Ghost.erased SB.bytes) ->
  stt bool (raw_terminal_rel kid key_k pm x' c)
    (fun res -> raw_terminal_rel kid key_k pm x' c ** pure (res == true <==> nlc kid key_k lsf c))

let nl_res (kid: asn1_id_t) (key_k: asn1_terminal_k) (lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (pm: perm) (x': asn1_terminal_impl_t key_k) (c: Ghost.erased SB.bytes) : Type =
  stt bool (raw_terminal_rel kid key_k pm x' c)
    (fun res -> raw_terminal_rel kid key_k pm x' c ** pure (res == true <==> nlc kid key_k lsf c))

inline_for_extraction
fn nl_nil (kid: asn1_id_t) (key_k: asn1_terminal_k) (pm: perm)
: nl_t kid key_k [] pm
= (x': asn1_terminal_impl_t key_k) (#c: Ghost.erased SB.bytes)
{
  true
}

inline_for_extraction
let eq_lit_t (kid: asn1_id_t) (key_k: asn1_terminal_k) (kx: asn1_key_lit key_k) (pm: perm) =
  (x': asn1_terminal_impl_t key_k) -> (#c: Ghost.erased SB.bytes) ->
  stt bool (raw_terminal_rel kid key_k pm x' c) (fun res -> raw_terminal_rel kid key_k pm x' c ** pure (res == true <==> Ghost.reveal c == WA.raw_key_enc kid key_k kx))

inline_for_extraction
fn nl_cons (kid: asn1_id_t) (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (kx: asn1_key_lit key_k)
  (y: Ghost.erased asn1_gen_items_lk) (tl: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (pm: perm)
  (eq: eq_lit_t kid key_k kx pm)
  (f: nl_t kid key_k tl pm)
: nl_t kid key_k ((kx, Ghost.reveal y) :: Ghost.reveal tl) pm
= (x': asn1_terminal_impl_t key_k) (#c: Ghost.erased SB.bytes)
{
  nlc_cons_eq kid key_k kx y tl c;
  let e = eq x' #c;
  if e {
    false
  } else {
    f x' #c
  }
}

(* Compare the key of the input to every literal of the table *)
[@@In.asn1_pulse_attr]
let rec not_lits (kid: asn1_id_t) ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k))
  ([@@@FStar.Attributes.monomorphize] lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (pm: perm)
  (x': asn1_terminal_impl_t key_k) (#c: Ghost.erased SB.bytes)
: Tot (nl_res kid key_k lsf pm x' c) (decreases lsf)
= [@inline_let] let vf : nl_t kid key_k lsf pm =
  (match lsf with
  | [] -> nl_nil kid key_k pm
  | (kx, y) :: tl -> nl_cons kid key_k () kx y tl pm
      (fun x' #c -> DE.dd_term kid key_k kx () pm x' #c)
      (fun x' #c -> not_lits kid key_k () tl pm x' #c))
  in vf x' #c

let ns_or_retry_post (x: SB.bytes) (a: prop) (p: nat) (v: SB.bytes) (r: jit_result) (p': nat) (v': SB.bytes)
: Lemma
  (requires (Seq.length v' == Seq.length v /\ p <= Seq.length v /\
    Seq.slice v' p (Seq.length v) == Seq.slice v p (Seq.length v) /\
    (r == JIT_NO_SPACE ==> Seq.length x > p)))
  (ensures (jit_post_g false x a p v (ns_or_retry r) p' v'))
= ()

let cat_ns (c1 c2: SB.bytes) (p: nat) (v: SB.bytes) (p1: nat) (v1: SB.bytes) (r: jit_result)
: Lemma
  (requires (W.r2l_post c2 p v true p1 v1 /\ (r == JIT_NO_SPACE ==> Seq.length c1 > p1)))
  (ensures (r == JIT_NO_SPACE ==> Seq.length (Seq.append c1 c2) > p))
= Seq.lemma_len_append c1 c2

let jit_retry_post (x: SB.bytes) (a: prop) (p: nat) (v: SB.bytes) (p': nat) (v': SB.bytes)
: Lemma
  (requires (Seq.length v' == Seq.length v /\ p <= Seq.length v /\
    Seq.slice v' p (Seq.length v) == Seq.slice v p (Seq.length v)))
  (ensures (jit_post_g false x a p v JIT_RETRY p' v'))
= ()

let jit_ok_post (x: SB.bytes) (a: prop) (p: nat) (v: SB.bytes) (p': nat) (v': SB.bytes)
: Lemma
  (requires (W.r2l_post x p v true p' v' /\ a))
  (ensures (jit_post_g false x a p v JIT_OK p' v'))
= ()

let jit_fb_ok (kid: asn1_id_t) (key_k: asn1_terminal_k) (lsf: list (asn1_key_lit key_k & asn1_gen_items_lk)) (fb: asn1_gen_items_lk)
  (c1 c2: SB.bytes) (p: nat) (v: SB.bytes) (p2: nat) (v2: SB.bytes)
: Lemma
  (requires (In.adb_key_supported key_k /\ W.r2l_post (Seq.append c1 c2) p v true p2 v2 /\
    nlc kid key_k lsf c1 /\
    L.acc #asn1_strong_parser_kind (parse_asn1_ILC kid (asn1_content_as_parser (ASN1_TERMINAL key_k))) c1 /\
    L.iacc (In.twins_of (dsnd fb)) c2))
  (ensures (jit_post_g false (Seq.append c1 c2) (JA.afbacc kid key_k lsf fb (Seq.append c1 c2)) p v JIT_OK p2 v2))
= JA.fbr_acc kid key_k fb c1 c2;
  nl_of_nlc kid key_k lsf c1 c2;
  nl_afb kid key_k lsf fb (Seq.append c1 c2);
  jit_ok_post (Seq.append c1 c2) (JA.afbacc kid key_k lsf fb (Seq.append c1 c2)) p v p2 v2

(* The fallback: the key of the input is first compared to every literal
   of the table (strict: if it is one of them, JIT_RETRY, even though the
   payload might happen to be accepted by that literal); then the payload
   and the key are written and checked, and the dispatch selects the
   fallback. Nothing is read back from the output. *)
inline_for_extraction
fn jit_fb (kid: asn1_id_t) (key_k: asn1_terminal_k) (u: squash (In.adb_key_supported key_k)) (lsf: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (fb: asn1_gen_items_lk) (#tfb: Type0) (dfb: idesc (dsnd fb) tfb) (pm: perm)
  (nlw: nl_t kid key_k lsf pm)
  (w1: jwx (raw_terminal_rel kid key_k) (L.acc #asn1_strong_parser_kind (parse_asn1_ILC kid (asn1_content_as_parser (ASN1_TERMINAL key_k)))) pm)
  (#ex2: bool) (w2: jwg ex2 (raw_irel false dfb) (L.iacc (In.twins_of (dsnd fb))) pm)
: jw #(asn1_terminal_impl_t key_k & tfb) (raw_dfbr kid key_k #fb dfb) (JA.afbacc kid key_k lsf fb) pm
= (x': (asn1_terminal_impl_t key_k & tfb)) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  rewrite (raw_dfbr kid key_k #fb dfb pm x' x) as (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) pm x' x);
  unfold (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) pm x' x);
  with c1 c2 . assert (raw_terminal_rel kid key_k pm (fst x') c1 ** raw_irel false dfb pm (snd x') c2);
  let n = nlw (fst x') #c1;
  if n {
    let ok = w2 (snd x') #c2 out pos;
    if (JIT_OK? ok) {
      with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
      let res = w1 (fst x') #c1 out pos;
      with v2 p2 . assert (SK.sbuf out v2 ** pts_to pos p2);
      frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
      fold (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) pm x' x);
      rewrite (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) pm x' x) as (raw_dfbr kid key_k #fb dfb pm x' x);
      if (JIT_OK? res) {
        W.r2l_post_append c1 c2 (SZ.v p) v (SZ.v p1) v1 true (SZ.v p2) v2;
        jit_fb_ok kid key_k lsf fb c1 c2 (SZ.v p) v (SZ.v p2) v2;
        JIT_OK
      } else {
        cat_ns c1 c2 (SZ.v p) v (SZ.v p1) v1 res;
        ns_or_retry_post x (JA.afbacc kid key_k lsf fb x) (SZ.v p) v res (SZ.v p2) v2;
        ns_or_retry res
      }
    } else {
      with v1 p1 . assert (SK.sbuf out v1 ** pts_to pos p1);
      Seq.lemma_len_append c1 c2;
      ns_or_retry_post x (JA.afbacc kid key_k lsf fb x) (SZ.v p) v ok (SZ.v p1) v1;
      fold (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) pm x' x);
      rewrite (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) pm x' x) as (raw_dfbr kid key_k #fb dfb pm x' x);
      ns_or_retry ok
    }
  } else {
    fold (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) pm x' x);
    rewrite (raw_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) pm x' x) as (raw_dfbr kid key_k #fb dfb pm x' x);
    jit_retry_post x (JA.afbacc kid key_k lsf fb x) (SZ.v p) v (SZ.v p) v;
    JIT_RETRY
  }
}

(* The whole schema *)

let jresg (ex: bool) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) (x': t) (x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (v: Ghost.erased SB.bytes) (p: Ghost.erased SZ.t) : Type =
  stt jit_result
    (SK.sbuf out v ** pts_to pos p ** r pm x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . SK.sbuf out v' ** pts_to pos p' ** r pm x' x **
      pure (jit_post_g ex x (a x) (SZ.v p) v res (SZ.v p') v'))

let jressg (ex: bool) (#t: Type0) (r: bprel t) (its: list gen_decorated_parser_twin) (pm: perm) (x': t) (x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (v: Ghost.erased SB.bytes) (p: Ghost.erased SZ.t) : Type =
  stt jit_result
    (SK.sbuf out v ** pts_to pos p ** r pm x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . SK.sbuf out v' ** pts_to pos p' ** r pm x' x **
      pure (jit_post_sg ex its x (SZ.v p) v res (SZ.v p') v'))

(* Exactness: the JIT writer of a schema never returns JIT_RETRY (so that
   JIT_INVALID means that the value has no valid encoding), unless the
   schema contains ANY (whose raw slices are checked to be exactly one
   TLV: with several TLVs, or none, the encoding might still be valid) or
   ANY DEFINED BY with a fallback (whose key is checked to be none of the
   literals: otherwise the payload might still be accepted by that
   literal). *)
[@@In.asn1_pulse_attr; FStar.Attributes.custard_compile_time]
let rec ex_content (k: asn1_content_k) : Tot bool (decreases k) =
  match k with
  | ASN1_TERMINAL _ -> true
  | ASN1_RESTRICTED_TERMINAL _ _ -> true
  | ASN1_SEQUENCE gitems -> ex_items (dsnd gitems)
  | ASN1_SEQUENCE_OF _ k' -> ex_k k'
  | ASN1_SET_OF _ k' -> ex_k k'
  | ASN1_SET _ items _ -> ex_items items
  | ASN1_PREFIXED k' -> ex_k k'
  | ASN1_ANY_DEFINED_BY _ prefix _ _ ls ofb _ _ -> ex_items prefix && ex_ls ls && None? ofb

and ex_k (#s: _) (k: asn1_k s) : Tot bool (decreases k) =
  match k with
  | ASN1_ILC _ k' -> ex_content k'
  | ASN1_CHOICE_ILC lc _ -> ex_lc lc
  | ASN1_ANY_ILC -> false

and ex_lc (lc: list (asn1_id_t & asn1_content_k)) : Tot bool (decreases lc) =
  match lc with
  | [] -> true
  | (_, ck) :: tl -> ex_content ck && ex_lc tl

and ex_ls (#t: eqtype) (ls: list (t & asn1_gen_items_lk)) : Tot bool (decreases ls) =
  match ls with
  | [] -> true
  | (_, y) :: tl -> ex_items (dsnd y) && ex_ls tl

and ex_items (#i: _) (ls: asn1_gen_items_l i) : Tot bool (decreases ls) =
  match ls with
  | ASN1_GEN_ITEMS_NIL -> true
  | ASN1_GEN_ITEMS_CONS _ _ dk _ tl -> ex_dec dk && ex_items tl

and ex_dec (#s: _) (#d: _) (dk: asn1_decorated_k s d) : Tot bool (decreases dk) =
  match dk with
  | ASN1_PLAIN_ILC k -> ex_k k
  | ASN1_OPTION_ILC k -> ex_k k
  | _ -> true

let jres (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) (x': t) (x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (v: Ghost.erased SB.bytes) (p: Ghost.erased SZ.t) : Type =
  jresg false r a pm x' x out pos v p

let jresx (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) (x': t) (x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (v: Ghost.erased SB.bytes) (p: Ghost.erased SZ.t) : Type =
  jresg true r a pm x' x out pos v p

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

let acc_terminal_prefixed_inv (id2: asn1_id_t) (k2: asn1_terminal_k) (b: SB.bytes)
: Lemma (requires (L.acc #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) b))
  (ensures (cacc id2 (ASN1_TERMINAL k2) b))
= ()

let acc_terminal_tlv_inv (id: asn1_id_t) (k: asn1_terminal_k) (b: SB.bytes)
: Lemma (requires (cacc id (ASN1_TERMINAL k) b))
  (ensures (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id #(ASN1_TERMINAL k) (asn1_terminal_as_parser k)) b))
= ()
#pop-options

inline_for_extraction
fn jit_terminal_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (pm: perm)
  (w: jwx (raw_terminal_rel id2 k2) (cacc id2 (ASN1_TERMINAL k2)) pm)
: jwx #(asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2)) (cacc id (ASN1_TERMINAL (ASN1_PREFIXED_TERMINAL id2 k2))) pm
= (x': asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  terminal_prefixed_eq id id2 k2 pm x' x;
  let x2 = prefixed_down id2 k2 x';
  rewrite (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x' x) as (raw_tlv id (raw_terminal_rel id2 k2) pm x2 x);
  let res = jit_tlv id (raw_terminal_rel id2 k2) #(ASN1_TERMINAL (ASN1_PREFIXED_TERMINAL id2 k2)) (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) pm
    (jit_iff (raw_terminal_rel id2 k2) (raw_terminal_rel id2 k2) ()
      (cacc id2 (ASN1_TERMINAL k2)) (L.acc #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2))) (acc_terminal_prefixed id2 k2) (acc_terminal_prefixed_inv id2 k2) pm w)
    x2 #x out pos;
  rewrite (raw_tlv id (raw_terminal_rel id2 k2) pm x2 x) as (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x' x);
  if (JIT_OK? res) {
    acc_terminal_tlv id (ASN1_PREFIXED_TERMINAL id2 k2) x;
    JIT_OK
  } else {
    Classical.move_requires (acc_terminal_tlv_inv id (ASN1_PREFIXED_TERMINAL id2 k2)) x;
    res
  }
}

[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_leaf_tlv (id: asn1_id_t) (k: E.leaf_k) (u: squash (In.supported_terminal k)) (pm: perm)
: jwx (raw_terminal_rel id k) (cacc id (ASN1_TERMINAL k)) pm
= terminal_leaf_equiv id k;
  jit_iff (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) ()
    (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id #(ASN1_TERMINAL k) (asn1_terminal_as_parser k))) (cacc id (ASN1_TERMINAL k)) (acc_terminal_tlv id k) (acc_terminal_tlv_inv id k) pm
    (jit_tlv id (raw_leaf k) #(ASN1_TERMINAL k) (asn1_terminal_as_parser k) pm
      (jit_pre (raw_leaf k) (L.tacc k) (L.acc #asn1_weak_parser_kind (asn1_terminal_as_parser k)) (fun _ -> ()) pm
        (JT.pv k () pm) (SK.sw_leaf k pm)))

[@@In.asn1_pulse_attr]
let rec jit_write_terminal (id: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) (u: squash (In.supported_terminal k)) (pm: perm)
  (x': asn1_terminal_impl_t k) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jresx (raw_terminal_rel id k) (cacc id (ASN1_TERMINAL k)) pm x' x out pos v p)
  (decreases k)
= [@inline_let] let vf : jwx (raw_terminal_rel id k) (cacc id (ASN1_TERMINAL k)) pm =
  (match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    jit_terminal_prefixed id id2 k2 pm
      (fun x' #x out pos #v #p -> jit_write_terminal id2 k2 () pm x' #x out pos #v #p)
  | _ -> jit_leaf_tlv id k () pm)
  in vf x' #x out pos #v #p

[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_restricted_tlv (id: asn1_id_t) (k: E.leaf_k) (r: asn1_restriction k) (u: squash (In.supported_restriction k r)) (pm: perm)
: jwx (raw_terminal_rel id k) (cacc id (ASN1_RESTRICTED_TERMINAL k r)) pm
= terminal_leaf_equiv id k;
  jit_iff (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) ()
    (cacc id (ASN1_RESTRICTED_TERMINAL k r)) (cacc id (ASN1_RESTRICTED_TERMINAL k r)) (fun _ -> ()) (fun _ -> ()) pm
    (jit_tlv id (raw_leaf k) #(ASN1_RESTRICTED_TERMINAL k r) (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) pm
      (jit_pre (raw_leaf k) (JT.pand (L.tacc k) (L.holds k (restriction_pred r)))
        (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r))) (fun w -> L.acc_restricted k r w) pm
        (JT.pc_then (raw_leaf k) JT.ptrue (L.tacc k) (L.tacc k) (L.holds k (restriction_pred r)) (fun _ -> ()) pm
          (JT.pv k () pm) (JT.pr k r () pm))
        (SK.sw_leaf k pm)))

(* DEFAULT components: also check that the value is not the default one *)

[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_default (id0: asn1_id_t) (k: E.leaf_k) (defl: asn1_key_lit k) (u: squash (In.supported_default k)) (pm: perm)
: jwx (raw_drel (DD_DEFAULT id0 #k defl)) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) pm
= let defv = key_of_lit k defl in
  dec_default_equiv id0 #k defl;
  terminal_leaf_equiv id0 k;
  L.iacc_default_none (ASN1_DEFAULT_TERMINAL id0 #k defl);
  default_nd_equiv id0 k defl;
  jit_iff (raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)) (raw_drel (DD_DEFAULT id0 #k defl)) ()
    (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) (fun _ -> ()) (fun _ -> ()) pm
    (jit_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) () pm
      (fun x' #c -> DE.dd_term id0 k defl () pm x' #c)
    (jit_opt_ne (raw_terminal_rel id0 k) (Set.singleton id0) (JF.fr_terminal id0 k) (cacc id0 (Co.default_content k defv)) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) ()
      (L.iacc_default id0 #k defl) (fun w -> L.iacc_default_iff id0 #k defl w) pm
      (jit_iff (raw_tlv id0 (raw_leaf k)) (raw_terminal_rel id0 k) ()
        (cacc id0 (Co.default_content k defv)) (cacc id0 (Co.default_content k defv)) (fun _ -> ()) (fun _ -> ()) pm
        (jit_tlv id0 (raw_leaf k) #(Co.default_content k defv) (asn1_content_as_parser (Co.default_content k defv)) pm
          (jit_pre (raw_leaf k) (JT.pand (L.tacc k) (L.holds k (defaultv_filter defv)))
            (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (Co.default_content k defv))) (fun w -> L.acc_default k defv w) pm
            (JT.pc_then (raw_leaf k) JT.ptrue (L.tacc k) (L.tacc k) (L.holds k (defaultv_filter defv)) (fun _ -> ()) pm
              (JT.pv k () pm) (JT.pn k defl () pm))
            (SK.sw_leaf k pm))))))

[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_default_restricted (id0: asn1_id_t) (k: E.leaf_k) (r: asn1_restriction k) (defl: asn1_key_lit k { restriction_pred r (key_of_lit k defl) })
  (u: squash (In.supported_default_restricted k r)) (pm: perm)
: jwx (raw_drel (DD_DEFAULT_RESTRICTED id0 #k r defl)) (dacc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) pm
= let defv = key_of_lit k defl in
  dec_default_restricted_equiv id0 #k r defl;
  terminal_leaf_equiv id0 k;
  L.iacc_default_none (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl);
  default_nd_equiv id0 k defl;
  jit_iff (raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)) (raw_drel (DD_DEFAULT_RESTRICTED id0 #k r defl)) ()
    (dacc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) (dacc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) (fun _ -> ()) (fun _ -> ()) pm
    (jit_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k) (dacc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) () pm
      (fun x' #c -> DE.dd_term id0 k defl () pm x' #c)
    (jit_opt_ne (raw_terminal_rel id0 k) (Set.singleton id0) (JF.fr_terminal id0 k) (cacc id0 (Co.default_restricted_content k r defv)) (dacc (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) ()
      (L.iacc_default_restricted id0 #k r defl) (fun w -> L.iacc_default_restricted_iff id0 #k r defl w) pm
      (jit_iff (raw_tlv id0 (raw_leaf k)) (raw_terminal_rel id0 k) ()
        (cacc id0 (Co.default_restricted_content k r defv)) (cacc id0 (Co.default_restricted_content k r defv)) (fun _ -> ()) (fun _ -> ()) pm
        (jit_tlv id0 (raw_leaf k) #(Co.default_restricted_content k r defv) (asn1_content_as_parser (Co.default_restricted_content k r defv)) pm
          (jit_pre (raw_leaf k) (JT.pand (JT.pand (L.tacc k) (L.holds k (restriction_pred r))) (L.holds k (defaultv_filter defv)))
            (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (Co.default_restricted_content k r defv))) (fun w -> L.acc_default_restricted k r defv w) pm
            (JT.pc_then (raw_leaf k) JT.ptrue (JT.pand (L.tacc k) (L.holds k (restriction_pred r))) (L.tacc k) (L.holds k (defaultv_filter defv)) (fun _ -> ()) pm
              (JT.pc_then (raw_leaf k) JT.ptrue (L.tacc k) (L.tacc k) (L.holds k (restriction_pred r)) (fun _ -> ()) pm
                (JT.pv k () pm) (JT.pr k r () pm))
              (JT.pn k defl () pm))
            (SK.sw_leaf k pm))))))

(* DEFAULT of a PREFIXED terminal: the explicit default value is omitted
   (`dec`); any other value is accepted iff the terminal is
   (`JK.default_of_ne`, `JK.default_back`) *)
[@@In.asn1_pulse_attr]
inline_for_extraction
let jit_default_prefixed (id0: asn1_id_t) (k: asn1_terminal_k) (defl: asn1_key_lit k) (u: squash (In.supported_default k)) (pm: perm)
: jwx (raw_drel (DD_DEFAULT id0 #k defl)) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) pm
= dec_default_equiv id0 #k defl;
  L.iacc_default_none (ASN1_DEFAULT_TERMINAL id0 #k defl);
  default_nd_equiv id0 k defl;
  jit_iff (raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)) (raw_drel (DD_DEFAULT id0 #k defl)) ()
    (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) (fun _ -> ()) (fun _ -> ()) pm
    (jit_nd_ne (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k) (Set.singleton id0) (JF.fr_terminal id0 k)
      (cacc id0 (ASN1_TERMINAL k)) (dacc (ASN1_DEFAULT_TERMINAL id0 #k defl)) ()
      (fun w -> JK.default_of_ne id0 k defl w; L.iacc_default id0 #k defl w)
      (fun w -> L.iacc_default_iff id0 #k defl w; JK.default_back id0 k defl w)
      pm
      (fun x' #c -> DE.dd_term id0 k defl () pm x' #c)
      (fun x' #x out pos #v #p -> jit_write_terminal id0 k () pm x' #x out pos #v #p))

(* Descriptor views: write the viewed value *)
inline_for_extraction
fn jit_view (#ex: bool) (#t #ty: Type0) (r: bprel t) (view: ty -> t) (a: SB.bytes -> prop) (pm: perm) (w: jwg ex r a pm)
: jwg ex #ty (raw_view r view) a pm
= (x': ty) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_view r view pm x' x);
  let res = w (view x') #x out pos;
  fold (raw_view r view pm x' x);
  res
}


(* KEEP-BYTES nodes: write the value, ignore the bytes *)
inline_for_extraction
fn jit_keep (#ex: bool) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) (w: jwg ex r a (pm /. 2.0R))
: jwg ex #(kept t) (raw_keep r) a pm
= (x': kept t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_keep r pm x' x);
  let res = w x'.kval #x out pos;
  fold (raw_keep r pm x' x);
  res
}

(* The whole schema, by descriptor.
   Single pass: every check is on the input value, before writing it;
   the output is never read back (except by the sorted insertion of SET
   and SET OF elements.) JIT_RETRY means that the value was rejected by a
   check stricter than DER (see `ex_content`.) *)

[@@In.asn1_pulse_attr]
let rec jit_write_crel (id: asn1_id_t) (#[@@@FStar.Attributes.monomorphize] k: asn1_content_k) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: cdesc k t) (u: squash (In.supported_content k /\ Conf.wf_content id k)) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jresg (ex_content k) (raw_crel id d) (cacc id k) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : jwg (ex_content k) (raw_crel id d) (cacc id k) pm =
  (match d with
  | CD_PREFIXED #_ #k' d' ->
    content_prefixed_equiv id d';
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_tlv id (raw_arel d')) (raw_crel id d) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_PREFIXED k')))) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_tlv id (raw_arel d') (asn1_content_as_parser (ASN1_PREFIXED k')) pm
        (jit_iff (raw_arel d') (raw_arel d') () (kacc k') (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_PREFIXED k'))) (L.acc_prefixed k') (L.acc_prefixed_inv k') pm
          (fun x' #x out pos #v #p -> jit_write_arel d' () pm x' #x out pos #v #p))))
  | CD_SEQUENCE gitems di ->
    content_sequence_equiv id gitems di;
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_tlv id (raw_irel false di)) (raw_crel id d) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_SEQUENCE gitems)))) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_tlv id (raw_irel false di) (asn1_content_as_parser (ASN1_SEQUENCE gitems)) pm
        (jit_iff (raw_irel false di) (raw_irel false di) ()
          (L.iacc (In.twins_of (dsnd gitems))) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE gitems))) (L.acc_sequence gitems) (L.acc_sequence_inv gitems) pm
          (fun x' #x out pos #v #p -> jit_write_irel di () pm x' #x out pos #v #p))))
  | CD_SEQUENCE_OF ne #_ #k' d' ->
    content_seq_of_equiv id ne d';
    L.tlv_shaped_k k';
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_tlv id (raw_ml (raw_arel d'))) (raw_crel id d) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k')))) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_tlv id (raw_ml (raw_arel d')) (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k')) pm
        (jit_iff (raw_ml (raw_arel d')) (raw_ml (raw_arel d')) ()
          (L.acc #asn1_weak_parser_kind (parse_sized_list ne (asn1_as_parser k'))) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SEQUENCE_OF ne k'))) (L.acc_seq_of ne k') (fun _ -> ()) pm
          (jit_write_ml (ex_k k') (raw_arel d') ne (In.validate_k k' ()) () (fun _ -> tf_of_fr (raw_arel d') _ (JF.fr_arel d' ())) (fun pm -> (fun x' #x out pos #v #p -> jit_write_arel d' () pm x' #x out pos #v #p)) (share_arel d') (gather_arel d') pm))))
  | CD_SET_OF ne #_ #k' d' ->
    content_set_of_equiv id ne d';
    L.tlv_shaped_k k';
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_tlv id (raw_ml_sorted (raw_arel d'))) (raw_crel id d) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_SET_OF ne k')))) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_tlv id (raw_ml_sorted (raw_arel d')) (asn1_content_as_parser (ASN1_SET_OF ne k')) pm
        (jit_iff (raw_ml_sorted (raw_arel d')) (raw_ml_sorted (raw_arel d')) ()
          (L.acc #asn1_weak_parser_kind (parse_sized_set ne (asn1_as_parser k'))) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET_OF ne k'))) (L.acc_set_of ne k') (fun _ -> ()) pm
          (jit_write_ml_sorted (ex_k k') (raw_arel d') ne (In.validate_k k' ()) () (fun _ -> tf_of_fr (raw_arel d') _ (JF.fr_arel d' ())) (fun pm -> (fun x' #x out pos #v #p -> jit_write_arel d' () pm x' #x out pos #v #p)) (share_arel d') (gather_arel d') pm))))
  | CD_SET ids items pf di ->
    content_set_equiv id ids items pf di;
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_tlv id (raw_irel true di)) (raw_crel id d) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser (ASN1_SET ids items pf)))) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_tlv id (raw_irel true di) (asn1_content_as_parser (ASN1_SET ids items pf)) pm
        (jit_iff (raw_irel true di) (raw_irel true di) ()
          (L.sacc (In.twins_of items)) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_SET ids items pf))) (L.acc_set ids items pf) (SetL.acc_set_inv ids items pf) pm
          (jit_w_of_s (raw_irel true di) (In.twins_of items) pm
            (fun x' #x out pos #v #p -> jit_write_set_irel di () pm x' #x out pos #v #p)))))
  | CD_TERMINAL k' ->
    content_terminal_equiv id k';
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_terminal_rel id k') (raw_crel id d) ()
      (cacc id (ASN1_TERMINAL k')) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (fun x' #x out pos #v #p -> jit_write_terminal id k' () pm x' #x out pos #v #p))
  | CD_RESTRICTED k' r ->
    content_restricted_equiv id k' r;
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_terminal_rel id k') (raw_crel id d) ()
      (cacc id (ASN1_RESTRICTED_TERMINAL k' r)) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_restricted_tlv id k' r () pm))
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    content_adb_none_equiv id ipd prefix kid key_k ls pf pf' dsx dpre;
    app_nil_l ls;
    aan_acons_x kid key_k ls;
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx))) (raw_crel id d) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser k))) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_tlv id (raw_iarel dpre (raw_sxrel kid dsx)) (asn1_content_as_parser k) pm
        (jit_iff (raw_iarel dpre (raw_sxrel kid dsx)) (raw_iarel dpre (raw_sxrel kid dsx)) ()
          (aan kid key_k ls (In.twins_of prefix)) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser k))
          (fun w -> JA.acc_content_none ipd prefix kid key_k ls pf pf' w)
          (fun w -> JAS.acc_content_none_inv ipd prefix kid key_k ls pf pf' w) pm
          (fun x' #x out pos #v #p ->
            jit_write_iarel dpre () (Set.singleton kid) () (aan kid key_k ls) () (raw_sxrel kid dsx) (JAS.av_sfx_sxrel kid dsx) pm
              (jit_iff (raw_sxrel kid dsx) (raw_sxrel kid dsx) ()
                (JA.adbacc kid key_k ls) (aan kid key_k ls []) (fun w -> JA.aacc_nil_none kid key_k ls w) (fun w -> JAS.aacc_nil_none_inv kid key_k ls w) pm
                (fun x' #x out pos #v #p -> jit_write_sxrel kid dsx () [] ls () pm x' #x out pos #v #p))
              x' #x out pos #v #p))))
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre ->
    content_adb_some_equiv id ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    app_nil_l ls;
    aas_acons_x kid key_k ls fb;
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)))) (raw_crel id d) ()
      (L.acc #asn1_strong_parser_kind (parse_asn1_ILC id (asn1_content_as_parser k))) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb))) (asn1_content_as_parser k) pm
        (jit_iff (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb))) (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb))) ()
          (aas kid key_k ls fb (In.twins_of prefix)) (L.acc #asn1_weak_parser_kind (asn1_content_as_parser k))
          (fun w -> JA.acc_content_some ipd prefix kid key_k ls fb pf pf' w)
          (fun w -> JAS.acc_content_some_inv ipd prefix kid key_k ls fb pf pf' w) pm
          (fun x' #x out pos #v #p ->
            jit_write_iarel dpre () (Set.singleton kid) () (aas kid key_k ls fb) () (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)) (JAS.av_sfx_fxrel kid dfb dfx) pm
              (jit_iff (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)) (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)) ()
                (JA.afbacc kid key_k ls fb) (aas kid key_k ls fb []) (fun w -> JA.aacc_nil_some kid key_k ls fb w) (fun w -> JAS.aacc_nil_some_inv kid key_k ls fb w) pm
                (fun x' #x out pos #v #p -> jit_write_fxrel kid dfx () [] ls () fb (raw_dfbr kid key_k #fb dfb) pm
                  (jit_fb kid key_k () ls fb dfb pm
                    (fun x' #c -> not_lits kid key_k () ls pm x' #c)
                    (fun x' #x out pos #v #p -> jit_write_terminal kid key_k () pm x' #x out pos #v #p)
                    (fun x' #x out pos #v #p -> jit_write_irel dfb () pm x' #x out pos #v #p))
                  x' #x out pos #v #p))
              x' #x out pos #v #p))))
  | CD_VIEW d' ty view mk law ->
    content_view_equiv id d' ty view mk law;
    jit_cast (ex_content k) () (raw_crel id d) (cacc id k) pm (
    jit_iff (raw_view (raw_crel id d') view) (raw_crel id d) () (cacc id k) (cacc id k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_view (raw_crel id d') view (cacc id k) pm (fun x' #x out pos #v #p -> jit_write_crel id d' () pm x' #x out pos #v #p))))
  in vf x' #x out pos #v #p

(* ANY DEFINED BY: the prefix items, then the suffix (written first.) *)
and jit_write_iarel (#[@@@FStar.Attributes.monomorphize] i: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (#[@@@FStar.Attributes.monomorphize] sfx: Type0) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: iadesc ls sfx t)
  (u: squash (In.supported_items ls /\ Conf.wf_items ls))
  (ks: Ghost.erased (Set.set asn1_id_t)) (wf: squash (asn1_any_prefix_k_wf ks i))
  (aa: Ghost.erased (list gen_decorated_parser_twin -> SB.bytes -> prop)) (acons: squash (JAS.acons_x_ok aa))
  (sr: bprel sfx) (avs: JAS.av_sfx_t sr ks) (pm: perm) (#exs: bool) ([@@@FStar.Attributes.monomorphize] ws: jwg exs sr (Ghost.reveal aa []) pm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jresg (ex_items ls && exs) (raw_iarel d sr) (Ghost.reveal aa (In.twins_of ls)) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : jwg (ex_items ls && exs) (raw_iarel d sr) (Ghost.reveal aa (In.twins_of ls)) pm =
  (match d with
  | IA_NIL ->
    items_any_nil_equiv sr;
    jit_cast (ex_items ls && exs) () (raw_iarel d sr) (Ghost.reveal aa (In.twins_of ls)) pm (
    jit_iff sr (raw_iarel d sr) () (Ghost.reveal aa []) (Ghost.reveal aa (In.twins_of ls)) (fun _ -> ()) (fun _ -> ()) pm ws)
  | IA_SINGLE #s1 #d1 #dk dd ->
    items_any_single_equiv dd sr;
    L.twins_of_single dk;
    L.item_set_twin dk;
    SL.item_dec_twin dk;
    if JF.any_dec dk
    then
      jit_cast (ex_items ls && exs) () (raw_iarel d sr) (Ghost.reveal aa (In.twins_of ls)) pm (
      jit_iff (raw_cat (raw_drel dd) sr) (raw_iarel d sr) ()
        (Ghost.reveal aa [In.twin_of dk]) (Ghost.reveal aa (In.twins_of ls)) (fun _ -> ()) (fun _ -> ()) pm
        (jit_acons_a (In.twin_of dk) [] (PSL.dec_shaped dk) aa () (raw_drel dd) sr pm
          (fun x -> JF.dfe_any dk x)
          (SL.hs (In.twin_of dk)) ()
          (if PLAIN? d1
           then JF.av_none sr (SL.hs (In.twin_of dk)) ()
           else avs (SL.hs (In.twin_of dk)) ())
          (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p)
          ws))
    else
      jit_cast (ex_items ls && exs) () (raw_iarel d sr) (Ghost.reveal aa (In.twins_of ls)) pm (
      jit_iff (raw_cat (raw_drel dd) sr) (raw_iarel d sr) ()
        (Ghost.reveal aa [In.twin_of dk]) (Ghost.reveal aa (In.twins_of ls)) (fun _ -> ()) (fun _ -> ()) pm
        (jit_acons_x (In.twin_of dk) [] (PSL.dec_shaped dk) aa () (raw_drel dd) sr pm
          (JF.fe_drel dd ())
          (SL.hs (In.twin_of dk)) ()
          (if PLAIN? d1
           then JF.av_none sr (SL.hs (In.twin_of dk)) ()
           else avs (SL.hs (In.twin_of dk)) ())
          (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p)
          ws))
  | IA_CONS #s1 #d1 #dk dd #s2 #d2 #dk2 #ids2 #tl2 dtl ->
    items_any_cons_equiv dd dtl sr;
    L.twins_of_cons2 dk dk2 tl2;
    JAS.any_wf_tl ks (s1, d1) ((s2, d2) :: ids2);
    L.item_set_twin dk;
    SL.item_dec_twin dk;
    if JF.any_dec dk
    then
      jit_cast (ex_items ls && exs) () (raw_iarel d sr) (Ghost.reveal aa (In.twins_of ls)) pm (
      jit_iff (raw_cat (raw_drel dd) (raw_iarel dtl sr)) (raw_iarel d sr) ()
        (Ghost.reveal aa (In.twin_of dk :: In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (Ghost.reveal aa (In.twins_of ls)) (fun _ -> ()) (fun _ -> ()) pm
        (jit_acons_a (In.twin_of dk) (In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (PSL.dec_shaped dk) aa ()
          (raw_drel dd) (raw_iarel dtl sr) pm
          (fun x -> JF.dfe_any dk x)
          (SL.hs (In.twin_of dk)) ()
          (if PLAIN? d1
           then JF.av_none (raw_iarel dtl sr) (SL.hs (In.twin_of dk)) ()
           else JAS.av_iarel dtl ks (SL.hs (In.twin_of dk)) () sr avs)
          (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p)
          (fun x' #x out pos #v #p -> jit_write_iarel dtl () ks () aa () sr avs pm ws x' #x out pos #v #p)))
    else
      jit_cast (ex_items ls && exs) () (raw_iarel d sr) (Ghost.reveal aa (In.twins_of ls)) pm (
      jit_iff (raw_cat (raw_drel dd) (raw_iarel dtl sr)) (raw_iarel d sr) ()
        (Ghost.reveal aa (In.twin_of dk :: In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (Ghost.reveal aa (In.twins_of ls)) (fun _ -> ()) (fun _ -> ()) pm
        (jit_acons_x (In.twin_of dk) (In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (PSL.dec_shaped dk) aa ()
          (raw_drel dd) (raw_iarel dtl sr) pm
          (JF.fe_drel dd ())
          (SL.hs (In.twin_of dk)) ()
          (if PLAIN? d1
           then JF.av_none (raw_iarel dtl sr) (SL.hs (In.twin_of dk)) ()
           else JAS.av_iarel dtl ks (SL.hs (In.twin_of dk)) () sr avs)
          (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p)
          (fun x' #x out pos #v #p -> jit_write_iarel dtl () ks () aa () sr avs pm ws x' #x out pos #v #p))))
  in vf x' #x out pos #v #p

(* The dispatch on the key, without a fallback. `ls` is the suffix of the
   whole table `lsf` after `pre`. *)
and jit_write_sxrel (kid: asn1_id_t) (#[@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k)
  (#[@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: sxdesc key_k ls t)
  (u: squash (In.adb_key_supported key_k /\ Conf.wf_terminal kid key_k))
  (pre: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (lsf: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk)))
  (u': squash (In.supported_ls ls /\ Conf.wf_ls ls /\ Ghost.reveal pre `List.Tot.append` ls == Ghost.reveal lsf /\ List.Tot.noRepeats (List.Tot.map fst (Ghost.reveal lsf)))) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jresg (ex_ls ls) (raw_sxrel kid d) (JA.adbacc kid key_k lsf) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : jwg (ex_ls ls) (raw_sxrel kid d) (JA.adbacc kid key_k lsf) pm =
  (match d with
  | SX_NIL _ ->
    adb_nil_equiv kid key_k;
    jit_cast (ex_ls ls) () (raw_sxrel kid d) (JA.adbacc kid key_k lsf) pm (
    jit_iff (raw_false unit) (raw_sxrel kid d) () (JA.adbacc kid key_k lsf) (JA.adbacc kid key_k lsf) (fun _ -> ()) (fun _ -> ()) pm
      (jit_false unit (JA.adbacc kid key_k lsf) pm))
  | SX_SINGLE _ kx y di ->
    adb_single_equiv kid kx y di;
    jit_cast (ex_ls ls) () (raw_sxrel kid d) (JA.adbacc kid key_k lsf) pm (
    jit_iff (raw_dlit kid kx #y di) (raw_sxrel kid d) ()
      (JA.adbacc kid key_k lsf) (JA.adbacc kid key_k lsf) (fun _ -> ()) (fun _ -> ()) pm
      (jit_lit kid key_k kx (raw_irel false di) (JA.adbacc kid key_k lsf) (L.iacc (In.twins_of (dsnd y)))
        (fun c -> JK.lit_iff kid key_k kx y pre [] c) pm
        (fun x' #x out pos #v #p -> jit_write_irel di () pm x' #x out pos #v #p)))
  | SX_CONS _ kx y di #hd2 #tl2 dtl ->
    adb_cons_equiv kid kx y di dtl;
    JK.lit_pre_tail key_k kx y pre hd2 tl2;
    jit_iff (raw_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl)) (raw_sxrel kid d) ()
      (JA.adbacc kid key_k lsf) (JA.adbacc kid key_k lsf) (fun _ -> ()) (fun _ -> ()) pm
      (jit_either_same (raw_dlit kid kx #y di) (raw_sxrel kid dtl) (JA.adbacc kid key_k lsf) pm
        (jit_cast (ex_ls ls) () (raw_dlit kid kx #y di) (JA.adbacc kid key_k lsf) pm
          (jit_lit kid key_k kx (raw_irel false di) (JA.adbacc kid key_k lsf) (L.iacc (In.twins_of (dsnd y)))
            (fun c -> JK.lit_iff kid key_k kx y pre (hd2 :: tl2) c) pm
            (fun x' #x out pos #v #p -> jit_write_irel di () pm x' #x out pos #v #p)))
        (jit_cast (ex_ls ls) () (raw_sxrel kid dtl) (JA.adbacc kid key_k lsf) pm
          (fun x' #x out pos #v #p -> jit_write_sxrel kid dtl () (Ghost.hide (Ghost.reveal pre `List.Tot.append` [(kx, y)])) lsf () pm x' #x out pos #v #p))))
  in vf x' #x out pos #v #p

(* The same, with a fallback, whose writer is `wfb` *)
and jit_write_fxrel (kid: asn1_id_t) (#[@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k)
  (#[@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#[@@@FStar.Attributes.monomorphize] fbt: Type0) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: fxdesc key_k ls fbt t)
  (u: squash (In.adb_key_supported key_k /\ Conf.wf_terminal kid key_k))
  (pre: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk))) (lsf: Ghost.erased (list (asn1_key_lit key_k & asn1_gen_items_lk)))
  (u': squash (In.supported_ls ls /\ Conf.wf_ls ls /\ Ghost.reveal pre `List.Tot.append` ls == Ghost.reveal lsf /\ List.Tot.noRepeats (List.Tot.map fst (Ghost.reveal lsf))))
  ([@@@FStar.Attributes.monomorphize] fb: asn1_gen_items_lk) (fbr: bprel fbt) (pm: perm)
  ([@@@FStar.Attributes.monomorphize] wfb: jw fbr (JA.afbacc kid key_k lsf fb) pm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jres (raw_fxrel kid d fbr) (JA.afbacc kid key_k lsf fb) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : jw (raw_fxrel kid d fbr) (JA.afbacc kid key_k lsf fb) pm =
  (match d with
  | FX_NIL _ ->
    afb_nil_equiv kid key_k fbr;
    jit_iff fbr (raw_fxrel kid d fbr) () (JA.afbacc kid key_k lsf fb) (JA.afbacc kid key_k lsf fb) (fun _ -> ()) (fun _ -> ()) pm wfb
  | FX_SINGLE _ kx y di ->
    afb_single_equiv kid kx y di fbr;
    jit_iff (raw_either (raw_dlit kid kx #y di) fbr) (raw_fxrel kid d fbr) ()
      (JA.afbacc kid key_k lsf fb) (JA.afbacc kid key_k lsf fb) (fun _ -> ()) (fun _ -> ()) pm
      (jit_either_same (raw_dlit kid kx #y di) fbr (JA.afbacc kid key_k lsf fb) pm
        (jit_weak (raw_dlit kid kx #y di) (JA.afbacc kid key_k lsf fb) pm
          (jit_lit kid key_k kx (raw_irel false di) (JA.afbacc kid key_k lsf fb) (L.iacc (In.twins_of (dsnd y)))
            (fun c -> JK.lit_fb_iff kid key_k kx y pre [] fb c) pm
            (fun x' #x out pos #v #p -> jit_write_irel di () pm x' #x out pos #v #p)))
        wfb)
  | FX_CONS _ kx y di #hd2 #tl2 dtl ->
    afb_cons_equiv kid kx y di dtl fbr;
    JK.lit_pre_tail key_k kx y pre hd2 tl2;
    jit_iff (raw_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr)) (raw_fxrel kid d fbr) ()
      (JA.afbacc kid key_k lsf fb) (JA.afbacc kid key_k lsf fb) (fun _ -> ()) (fun _ -> ()) pm
      (jit_either_same (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr) (JA.afbacc kid key_k lsf fb) pm
        (jit_weak (raw_dlit kid kx #y di) (JA.afbacc kid key_k lsf fb) pm
          (jit_lit kid key_k kx (raw_irel false di) (JA.afbacc kid key_k lsf fb) (L.iacc (In.twins_of (dsnd y)))
            (fun c -> JK.lit_fb_iff kid key_k kx y pre (hd2 :: tl2) fb c) pm
            (fun x' #x out pos #v #p -> jit_write_irel di () pm x' #x out pos #v #p)))
        (fun x' #x out pos #v #p -> jit_write_fxrel kid dtl () (Ghost.hide (Ghost.reveal pre `List.Tot.append` [(kx, y)])) lsf () fb fbr pm wfb x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and jit_write_irel (#[@@@FStar.Attributes.monomorphize] i: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: idesc ls t)
  (u: squash (In.supported_items ls /\ asn1_sequence_k_wf i /\ Conf.wf_items ls)) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jresg (ex_items ls) (raw_irel false d) (L.iacc (In.twins_of ls)) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : jwg (ex_items ls) (raw_irel false d) (L.iacc (In.twins_of ls)) pm =
  (match d with
  | ID_NIL ->
    items_nil_equiv false;
    jit_cast (ex_items ls) () (raw_irel false d) (L.iacc (In.twins_of ls)) pm (
    jit_iff (raw_pure null_enc) (raw_irel false d) ()
      (L.iacc []) (L.iacc (In.twins_of ls)) (fun _ -> ()) (fun _ -> ()) pm (jit_nil pm))
  | ID_SINGLE #_ #_ #dk dd ->
    items_single_equiv false dd;
    L.twins_of_single dk;
    jit_cast (ex_items ls) () (raw_irel false d) (L.iacc (In.twins_of ls)) pm (
    jit_iff (raw_drel dd) (raw_irel false d) ()
      (dacc dk) (L.iacc (In.twins_of ls)) (fun _ -> ()) (fun _ -> ()) pm
      (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p))
  | ID_CONS #s1 #d1 #dk #t1 dd #s2 #d2 #dk2 #ids2 #tl2 #t2 dtl ->
    items_cons_equiv false dd dtl;
    join_cat_equiv false (raw_drel dd) (raw_irel false dtl);
    L.twins_of_cons2 dk dk2 tl2;
    SL.wf_tl (s1, d1) ((s2, d2) :: ids2);
    L.item_set_twin dk;
    SL.item_dec_twin dk;
    if JF.any_dec dk
    then
      (* An ANY head is checked to be exactly one TLV (or absent), so that
         it does not hide the next components *)
      jit_cast (ex_items ls) () (raw_irel false d) (L.iacc (In.twins_of ls)) pm (
      jit_iff
        #_ #(t1 & t2)
        (raw_cat (raw_drel dd) (raw_irel false dtl))
        (raw_irel false d) ()
        (L.iacc (In.twin_of dk :: In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (L.iacc (In.twins_of ls)) (fun _ -> ()) (fun _ -> ()) pm
        (jit_items_cons_a (In.twin_of dk) (In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
          (raw_drel dd) (raw_irel false dtl) pm
          (fun x -> JF.dfe_any dk x)
          (SL.hs (In.twin_of dk)) ()
          (if PLAIN? d1
           then JF.av_none (raw_irel false dtl) (SL.hs (In.twin_of dk)) ()
           else JF.av_irel dtl (SL.hs (In.twin_of dk)) ())
          (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p)
          (fun x' #x out pos #v #p -> jit_write_irel dtl () pm x' #x out pos #v #p)))
    else
      jit_cast (ex_items ls) () (raw_irel false d) (L.iacc (In.twins_of ls)) pm (
      jit_iff
        #_ #(t1 & t2)
        (raw_cat (raw_drel dd) (raw_irel false dtl))
        (raw_irel false d) ()
        (L.iacc (In.twin_of dk :: In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))) (L.iacc (In.twins_of ls)) (fun _ -> ()) (fun _ -> ()) pm
        (jit_items_cons_x (In.twin_of dk) (In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (PSL.dec_shaped dk)
          (raw_drel dd) (raw_irel false dtl) pm
          (JF.fe_drel dd ())
          (SL.hs (In.twin_of dk)) ()
          (if PLAIN? d1
           then JF.av_none (raw_irel false dtl) (SL.hs (In.twin_of dk)) ()
           else JF.av_irel dtl (SL.hs (In.twin_of dk)) ())
          (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p)
          (fun x' #x out pos #v #p -> jit_write_irel dtl () pm x' #x out pos #v #p))))
  in vf x' #x out pos #v #p

and jit_write_set_irel (#[@@@FStar.Attributes.monomorphize] i: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: idesc ls t)
  (u: squash (In.supported_items ls /\ asn1_set_k_wf i /\ Conf.wf_items ls)) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jressg (ex_items ls) (raw_irel true d) (In.twins_of ls) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : jwsg (ex_items ls) (raw_irel true d) (In.twins_of ls) pm =
  (match d with
  | ID_NIL ->
    items_nil_equiv true;
    jit_s_cast (ex_items ls) () (raw_irel true d) (In.twins_of ls) pm (
    jit_s_ext (raw_pure null_enc) (raw_irel true d) [] (In.twins_of ls) () pm (jit_s_nil pm))
  | ID_SINGLE #_ #_ #dk dd ->
    items_single_equiv true dd;
    L.twins_of_single dk;
    L.set_cons_ok_intro dk ASN1_GEN_ITEMS_NIL;
    PSL.dec_shaped dk;
    if JF.any_dec dk
    then
      jit_s_cast (ex_items ls) () (raw_irel true d) (In.twins_of ls) pm (
      jit_s_of_w (raw_irel true d) (In.twins_of ls) pm
        (jit_ext (raw_drel dd) (raw_irel true d) ()
          (L.sacc1 (In.twin_of dk)) (L.sacc (In.twins_of ls)) (L.sacc_single (In.twin_of dk)) pm
          (jit_set_elt_a (In.twin_of dk) () (fun x -> JF.dfe_any dk x) (raw_drel dd) pm
            (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p))))
    else
      jit_s_cast (ex_items ls) () (raw_irel true d) (In.twins_of ls) pm (
      jit_s_ext (raw_drel dd) (raw_irel true d) [In.twin_of dk] (In.twins_of ls) () pm
        (jit_set_single_x (In.twin_of dk) () (raw_drel dd) pm (JF.fe_drel dd ())
          (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p)))
  | ID_CONS #s1 #d1 #dk #t1 dd #s2 #d2 #dk2 #ids2 #tl2 #t2 dtl ->
    items_cons_equiv true dd dtl;
    join_ins_equiv true (raw_drel dd) (raw_irel true dtl);
    L.twins_of_cons2 dk dk2 tl2;
    L.set_cons_ok_intro dk (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2);
    PSL.dec_shaped dk;
    if JF.any_dec dk
    then
      jit_s_cast (ex_items ls) () (raw_irel true d) (In.twins_of ls) pm (
      jit_s_ext
        #_ #(t1 & t2)
        (raw_ins SI.lt_tag (raw_drel dd) (raw_irel true dtl))
        (raw_irel true d)
        (In.twin_of dk :: In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (In.twins_of ls) () pm
        (jit_set_cons (In.twin_of dk) (In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) ()
          (raw_drel dd) (raw_irel true dtl) pm
          (jit_set_elt_a (In.twin_of dk) () (fun x -> JF.dfe_any dk x) (raw_drel dd) pm
            (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p))
          (fun x' #x out pos #v #p -> jit_write_set_irel dtl () pm x' #x out pos #v #p)))
    else
      jit_s_cast (ex_items ls) () (raw_irel true d) (In.twins_of ls) pm (
      jit_s_ext
        #_ #(t1 & t2)
        (raw_ins SI.lt_tag (raw_drel dd) (raw_irel true dtl))
        (raw_irel true d)
        (In.twin_of dk :: In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) (In.twins_of ls) () pm
        (jit_set_cons_x (In.twin_of dk) (In.twins_of (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) ()
          (raw_drel dd) (raw_irel true dtl) pm
          (JF.fe_drel dd ())
          (fun x' #x out pos #v #p -> jit_write_drel dd () pm x' #x out pos #v #p)
          (fun x' #x out pos #v #p -> jit_write_set_irel dtl () pm x' #x out pos #v #p))))
  in vf x' #x out pos #v #p

and jit_write_drel (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] dc: _) (#[@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s dc) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: ddesc dk t)
  (u: squash (In.supported_dec dk /\ Conf.wf_dec dk)) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jresg (ex_dec dk) (raw_drel d) (dacc dk) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : jwg (ex_dec dk) (raw_drel d) (dacc dk) pm =
  (match d with
  | DD_PLAIN #_ #k d' ->
    dec_plain_equiv d';
    jit_cast (ex_dec dk) () (raw_drel d) (dacc dk) pm (
    jit_iff (raw_arel d') (raw_drel d) () (kacc k) (dacc dk) (L.iacc_plain k) (fun w -> L.iacc_plain_iff k w) pm
      (fun x' #x out pos #v #p -> jit_write_arel d' () pm x' #x out pos #v #p))
  | DD_OPTION #_ #k d' ->
    dec_option_equiv d';
    L.iacc_option_none k;
    if ASN1_ANY_ILC? k
    then begin match d' with
      | D_ANY ->
        rel_any_equiv ();
        jit_cast (ex_dec dk) () (raw_drel d) (dacc dk) pm (
        jit_iff (raw_opt raw_slice) (raw_drel d) () (dacc dk) (dacc dk) (fun _ -> ()) (fun _ -> ()) pm
          (jit_opt_slice (kacc k) (dacc dk) () (L.iacc_option_some k) (fun w -> L.iacc_option_iff k w) pm
            (jit_iff (raw_arel d') raw_slice () (kacc k) (kacc k) (fun _ -> ()) (fun _ -> ()) pm
              (fun x' #x out pos #v #p -> jit_write_arel d' () pm x' #x out pos #v #p))))
      | _ ->
        (* a view of ANY: an empty encoding would be absent *)
        jit_cast (ex_dec dk) () (raw_drel d) (dacc dk) pm (
        jit_iff (raw_opt (raw_arel d')) (raw_drel d) () (dacc dk) (dacc dk) (fun _ -> ()) (fun _ -> ()) pm
          (jit_opt_a (raw_arel d') (kacc k) (dacc dk) () (L.iacc_option_some k) pm
            (fun x' #x out pos #v #p -> jit_write_arel d' () pm x' #x out pos #v #p)))
    end else
      jit_cast (ex_dec dk) () (raw_drel d) (dacc dk) pm (
      jit_iff (raw_opt (raw_arel d')) (raw_drel d) () (dacc dk) (dacc dk) (fun _ -> ()) (fun _ -> ()) pm
        (jit_opt_ne (raw_arel d') s (JF.fr_arel d' ()) (kacc k) (dacc dk) () (L.iacc_option_some k) (fun w -> L.iacc_option_iff k w) pm
          (fun x' #x out pos #v #p -> jit_write_arel d' () pm x' #x out pos #v #p)))
  | DD_DEFAULT id0 #k defl ->
    if ASN1_PREFIXED_TERMINAL? k
    then jit_cast (ex_dec dk) () (raw_drel d) (dacc dk) pm (jit_default_prefixed id0 k defl () pm)
    else jit_cast (ex_dec dk) () (raw_drel d) (dacc dk) pm (jit_default id0 k defl () pm)
  | DD_DEFAULT_RESTRICTED id0 #k r defl ->
    jit_cast (ex_dec dk) () (raw_drel d) (dacc dk) pm (jit_default_restricted id0 k r defl () pm)
  | DD_VIEW d' ty view mk law ->
    dec_view_equiv d' ty view mk law;
    jit_cast (ex_dec dk) () (raw_drel d) (dacc dk) pm (
    jit_iff (raw_view (raw_drel d') view) (raw_drel d) () (dacc dk) (dacc dk) (fun _ -> ()) (fun _ -> ()) pm
      (jit_view (raw_drel d') view (dacc dk) pm (fun x' #x out pos #v #p -> jit_write_drel d' () pm x' #x out pos #v #p))))
  in vf x' #x out pos #v #p

and jit_write_arel (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] k: asn1_k s) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: adesc k t)
  (u: squash (In.supported_k k /\ Conf.wf k)) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jresg (ex_k k) (raw_arel d) (kacc k) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : jwg (ex_k k) (raw_arel d) (kacc k) pm =
  (match d with
  | D_ILC id #k' cd ->
    rel_ilc_equiv id cd;
    jit_cast (ex_k k) () (raw_arel d) (kacc k) pm (
    jit_iff (raw_crel id cd) (raw_arel d) () (cacc id k') (kacc k) (L.acc_k_ilc id k') (L.acc_k_ilc_inv id k') pm
      (fun x' #x out pos #v #p -> jit_write_crel id cd () pm x' #x out pos #v #p))
  | D_CHOICE lc pf ld ->
    rel_choice_equiv lc pf ld;
    jit_cast (ex_k k) () (raw_arel d) (kacc k) pm (
    jit_iff (raw_lcrel ld) (raw_arel d) () (L.lacc lc) (kacc k) (L.lacc_choice lc pf) (L.lacc_choice_inv lc pf) pm
      (fun x' #x out pos #v #p -> jit_write_lcrel ld () pm x' #x out pos #v #p))
  | D_ANY ->
    rel_any_equiv ();
    jit_cast (ex_k k) () (raw_arel d) (kacc k) pm (
    jit_iff raw_slice (raw_arel d) () (kacc k) (kacc k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_pre raw_slice (kacc k) (kacc k) (fun _ -> ()) pm
        (JT.pc_slice (In.validate_k ASN1_ANY_ILC ()) JT.ptrue (kacc k) (fun _ -> ()) pm)
        (SK.sw_slice pm)))
  | D_VIEW d' ty view mk law ->
    rel_view_equiv d' ty view mk law;
    jit_cast (ex_k k) () (raw_arel d) (kacc k) pm (
    jit_iff (raw_view (raw_arel d') view) (raw_arel d) () (kacc k) (kacc k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_view (raw_arel d') view (kacc k) pm (fun x' #x out pos #v #p -> jit_write_arel d' () pm x' #x out pos #v #p)))
  | D_KEEP d' wf ->
    rel_keep_equiv d' wf;
    jit_cast (ex_k k) () (raw_arel d) (kacc k) pm (
    jit_iff (raw_keep (raw_arel d')) (raw_arel d) () (kacc k) (kacc k) (fun _ -> ()) (fun _ -> ()) pm
      (jit_keep (raw_arel d') (kacc k) pm (fun x' #x out pos #v #p -> jit_write_arel d' () (pm /. 2.0R) x' #x out pos #v #p))))
  in vf x' #x out pos #v #p

and jit_write_lcrel (#[@@@FStar.Attributes.monomorphize] lc: list (asn1_id_t & asn1_content_k)) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: lcdesc lc t)
  (u: squash (lc_ok lc /\ Conf.wf_lc lc)) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (jresg (ex_lc lc) (raw_lcrel d) (L.lacc lc) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : jwg (ex_lc lc) (raw_lcrel d) (L.lacc lc) pm =
  (match d with
  | LC_NIL ->
    lc_nil_equiv ();
    jit_cast (ex_lc lc) () (raw_lcrel d) (L.lacc lc) pm (
    jit_iff (raw_false unit) (raw_lcrel d) () (L.lacc lc) (L.lacc lc) (fun _ -> ()) (fun _ -> ()) pm (jit_false unit (L.lacc lc) pm))
  | LC_SINGLE id' #c cd ->
    lc_single_equiv id' cd;
    let u' = L.lc_tail_ok (id', c) [] u in
    jit_cast (ex_lc lc) () (raw_lcrel d) (L.lacc lc) pm (
    jit_iff_fr (raw_crel id' cd) (raw_lcrel d) () (FStar.Set.singleton id') (JF.fr_crel id' cd)
      (cacc id' c) (L.lacc lc) (L.lacc_hd id' c []) (L.lacc_hd_inv id' c []) pm
      (fun x' #x out pos #v #p -> jit_write_crel id' cd () pm x' #x out pos #v #p))
  | LC_CONS id' #c cd #hd2 #tl2 dtl ->
    lc_cons_equiv id' cd dtl;
    let u' = L.lc_tail_ok (id', c) (hd2 :: tl2) u in
    jit_cast (ex_lc lc) () (raw_lcrel d) (L.lacc lc) pm (
    jit_iff (raw_either (raw_crel id' cd) (raw_lcrel dtl)) (raw_lcrel d) () (L.lacc lc) (L.lacc lc) (fun _ -> ()) (fun _ -> ()) pm
      (jit_either_x (raw_crel id' cd) (raw_lcrel dtl) (cacc id' c) (L.lacc (hd2 :: tl2)) (L.lacc lc)
        (FStar.Set.singleton id') (JF.lc_set (hd2 :: tl2)) (JF.fr_crel id' cd) (JF.fr_lcrel dtl)
        (L.lacc_hd id' c (hd2 :: tl2)) (L.lacc_tl id' c (hd2 :: tl2))
        (L.lacc_hd_inv id' c (hd2 :: tl2)) (L.lacc_tl_inv id' c (hd2 :: tl2)) pm
        (fun x' #x out pos #v #p -> jit_write_crel id' cd () pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> jit_write_lcrel dtl () pm x' #x out pos #v #p))))
  in vf x' #x out pos #v #p

(* The top level. JIT_RETRY (strict rejection) becomes JIT_INVALID: the
   value has no valid encoding if `ex_k k`, or else it was rejected by a
   check stricter than DER (an ANY slice that is not exactly one TLV, or
   the fallback of ANY DEFINED BY with the key of one of the literals.) *)

let jit_post_r (ex: bool) (x: SB.bytes) (a: prop) (p: nat) (v: SB.bytes) (res: jit_result) (p': nat) (v': SB.bytes) : prop =
  Seq.length v' == Seq.length v /\
  p <= Seq.length v /\
  Seq.slice v' p (Seq.length v) == Seq.slice v p (Seq.length v) /\
  (res == JIT_OK ==> (W.r2l_post x p v true p' v' /\ a)) /\
  (res == JIT_NO_SPACE ==> Seq.length x > p) /\
  (res == JIT_INVALID ==> (ex == true ==> ~ a)) /\
  ~ (JIT_RETRY? res)

inline_for_extraction
let jwrs (ex: bool) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) =
  (x': t) -> (#x: Ghost.erased SB.bytes) ->
  (out: SK.sink) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt jit_result
    (SK.sbuf out v ** pts_to pos p ** r pm x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . SK.sbuf out v' ** pts_to pos p' ** r pm x' x **
      pure (jit_post_r ex x (a x) (SZ.v p) v res (SZ.v p') v'))

inline_for_extraction
fn jit_root (#ex: bool) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) (w: jwg ex r a pm)
: jwrs ex #t r a pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: SK.sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let res = w x' #x out pos;
  match res {
    JIT_RETRY -> { JIT_INVALID }
    _ -> { res }
  }
}

(* Writing to an output buffer *)

inline_for_extraction
let jwr (ex: bool) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) =
  (x': t) -> (#x: Ghost.erased SB.bytes) ->
  (out: S.slice U8.t) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt jit_result
    (pts_to out v ** pts_to pos p ** r pm x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** r pm x' x **
      pure (jit_post_r ex x (a x) (SZ.v p) v res (SZ.v p') v'))

inline_for_extraction
fn jit_wet (#ex: bool) (#t: Type0) (#r: bprel t) (#a: SB.bytes -> prop) (#pm: perm) (w: jwrs ex r a pm)
: jwr ex #t r a pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  SK.sbuf_wet_intro (SK.Wet out) out;
  let res = w x' #x (SK.Wet out) pos;
  SK.sbuf_wet_elim (SK.Wet out) out;
  res
}

(* Computing the size of the encoding (and checking it as when writing),
   within a budget: on success, the size is subtracted from the budget;
   JIT_NO_SPACE if the encoding is larger than the budget *)

let jit_size_post (ex: bool) (x: SB.bytes) (a: prop) (b: nat) (res: jit_result) (b': nat) : prop =
  (res == JIT_OK ==> (a /\ b' + Seq.length x == b)) /\
  (res == JIT_NO_SPACE ==> Seq.length x > b) /\
  (res == JIT_INVALID ==> (ex == true ==> ~ a)) /\
  ~ (JIT_RETRY? res)

inline_for_extraction
let jsr (ex: bool) (#t: Type0) (r: bprel t) (a: SB.bytes -> prop) (pm: perm) =
  (x': t) -> (#x: Ghost.erased SB.bytes) ->
  (budget: ref SZ.t) -> (#b: Ghost.erased SZ.t) ->
  stt jit_result
    (pts_to budget b ** r pm x' x)
    (fun res -> exists* b' . pts_to budget b' ** r pm x' x **
      pure (jit_size_post ex x (a x) (SZ.v b) res (SZ.v b')))

inline_for_extraction
fn jit_dry (#ex: bool) (#t: Type0) (#r: bprel t) (#a: SB.bytes -> prop) (#pm: perm) (w: jwrs ex r a pm)
: jsr ex #t r a pm
= (x': t) (#x: Ghost.erased SB.bytes) (budget: ref SZ.t) (#b: Ghost.erased SZ.t)
{
  fold (SK.sbuf SK.Dry (Seq.create (SZ.v b) 0uy));
  let res = w x' #x SK.Dry budget #(Seq.create (SZ.v b) 0uy);
  with v' . assert (SK.sbuf SK.Dry v');
  unfold (SK.sbuf SK.Dry v');
  res
}

inline_for_extraction
let jit_writer_d (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (u: squash (RW.raw_ok k)) (pm: perm) : jwr (ex_k k) (raw_arel d) (kacc k) pm =
  jit_wet (jit_root (raw_arel d) (kacc k) pm (fun x' #x out pos #v #p -> jit_write_arel d () pm x' #x out pos #v #p))

inline_for_extraction
let jit_size_d (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (u: squash (RW.raw_ok k)) (pm: perm) : jsr (ex_k k) (raw_arel d) (kacc k) pm =
  jit_dry (jit_root (raw_arel d) (kacc k) pm (fun x' #x out pos #v #p -> jit_write_arel d () pm x' #x out pos #v #p))

(* The legacy writer: nested pairs and `either` *)
inline_for_extraction
let jit_writer (#s: _) (k: asn1_k s) (u: squash (RW.raw_ok k)) (pm: perm) : jwr (ex_k k) (raw_rel k) (kacc k) pm =
  jit_wet (jit_root (raw_rel k) (kacc k) pm (fun x' #x out pos #v #p -> jit_write_arel (legacy_adesc k) () pm x' #x out pos #v #p))

inline_for_extraction
let jit_size (#s: _) (k: asn1_k s) (u: squash (RW.raw_ok k)) (pm: perm) : jsr (ex_k k) (raw_rel k) (kacc k) pm =
  jit_dry (jit_root (raw_rel k) (kacc k) pm (fun x' #x out pos #v #p -> jit_write_arel (legacy_adesc k) () pm x' #x out pos #v #p))
