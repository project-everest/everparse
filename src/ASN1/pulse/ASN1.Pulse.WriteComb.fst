module ASN1.Pulse.WriteComb
#lang-pulse

(* Combinators for the right-to-left writer interpreter
   (ASN1.Pulse.Writer): changing the relation and the encoder, OPTIONAL and
   DEFAULT fields, pairs of fields, CHOICE alternatives, ANY, restricted
   terminals, and SEQUENCE OF / SET OF (through the mixed-list writer, with
   a generic TLV jumper over the elements). *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module SB = LowParse.Spec.Base
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module It = LowParse.PulseParse.Iterator
module WI = LowParse.PulseParse.Iterator.R2L
module W = LowParse.Pulse.R2L
module Conf = ASN1.Spec.Conformance
module Ser = ASN1.Spec.Serializer
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC
module PSO = ASN1.Pulse.ParseSeqOf
module WL = ASN1.Pulse.WriteLeaf
module RS = ASN1.Pulse.RelShare
module WLm = ASN1.Pulse.Writer.Lemmas

(* Changing the relation and the encoder *)

inline_for_extraction
fn write_ext
  (#t' #t: Type0) (r1 r2: prel t' t) (sq: squash (RS.prel_equiv r1 r2))
  (#enc1: t -> GTot SB.bytes) (enc2: t -> GTot SB.bytes) (eq: (x: t) -> Lemma (enc1 x == enc2 x))
  (pm: perm)
  (w: W.r2l_writer_f (r1 pm) enc1)
: W.r2l_writer_f #t' #t (r2 pm) enc2
= (x': t') (#x: Ghost.erased t) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  rewrite (r2 pm x' x) as (r1 pm x' x);
  let res = w x' out pos;
  rewrite (r1 pm x' x) as (r2 pm x' x);
  eq x;
  res
}

(* Nothing to write *)

let empty_enc (_: unit) : GTot SB.bytes = Seq.empty

inline_for_extraction
fn write_emp_unit (pm: perm)
: W.r2l_writer_f #unit #unit (prel_emp unit unit pm) empty_enc
= (x': unit) (#x: Ghost.erased unit) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  W.r2l_post_empty (SZ.v p) v;
  true
}

(* OPTIONAL *)

ghost
fn option_none_elim (#t: Type0) (#u: Type0) (r: prel t u) (pm: perm) (y: option u)
requires prel_option r pm None y
ensures prel_option r pm None y ** pure (y == None)
{
  match y {
    None -> { () }
    Some b -> {
      rewrite (prel_option r pm None y) as pure False;
      unreachable ()
    }
  }
}

ghost
fn option_some_elim (#t: Type0) (#u: Type0) (r: prel t u) (pm: perm) (a: t) (y: option u)
requires prel_option r pm (Some a) y
returns b: Ghost.erased u
ensures r pm a b ** pure (y == Some (Ghost.reveal b))
{
  match y {
    None -> {
      rewrite (prel_option r pm (Some a) y) as pure False;
      unreachable ()
    }
    Some b -> {
      rewrite (prel_option r pm (Some a) y) as (r pm a b);
      Ghost.hide b
    }
  }
}

inline_for_extraction
fn write_option (#t' #t: Type0) (r: prel t' t) (#enc: t -> GTot SB.bytes) (pm: perm) (w: W.r2l_writer_f (r pm) enc)
: W.r2l_writer_f #(option t') #(option t) (prel_option r pm) (WLm.option_enc enc)
= (x': option t') (#x: Ghost.erased (option t)) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (prel_option r pm x' x) as (prel_option r pm None x);
      option_none_elim r pm x;
      rewrite (prel_option r pm None x) as (prel_option r pm x' x);
      W.r2l_post_empty (SZ.v p) v;
      true
    }
    Some a -> {
      rewrite (prel_option r pm x' x) as (prel_option r pm (Some a) x);
      let b = option_some_elim r pm a x;
      let res = w a #b out pos;
      rewrite (r pm a b) as (prel_option r pm x' x);
      res
    }
  }
}

(* DEFAULT *)

ghost
fn default_none_elim (#t: Type0) (#u: eqtype) (r: prel t u) (defv: u) (pm: perm) (y: default_tv defv)
requires RS.prel_default r defv pm None y
ensures RS.prel_default r defv pm None y ** pure (y == Default)
{
  match y {
    Default -> { () }
    Nondefault b -> {
      rewrite (RS.prel_default r defv pm None y) as pure False;
      unreachable ()
    }
  }
}

ghost
fn default_some_elim (#t: Type0) (#u: eqtype) (r: prel t u) (defv: u) (pm: perm) (a: t) (y: default_tv defv)
requires RS.prel_default r defv pm (Some a) y
returns b: Ghost.erased u
ensures r pm a b ** pure (Nondefault? y /\ Nondefault?.v' y == Ghost.reveal b)
{
  match y {
    Default -> {
      rewrite (RS.prel_default r defv pm (Some a) y) as pure False;
      unreachable ()
    }
    Nondefault b -> {
      rewrite (RS.prel_default r defv pm (Some a) y) as (r pm a b);
      Ghost.hide b
    }
  }
}

inline_for_extraction
fn write_default (#t' : Type0) (#t: eqtype) (r: prel t' t) (defv: t) (#enc: t -> GTot SB.bytes) (pm: perm) (w: W.r2l_writer_f (r pm) enc)
: W.r2l_writer_f #(option t') #(default_tv defv) (RS.prel_default r defv pm) (WLm.default_enc #t #defv enc)
= (x': option t') (#x: Ghost.erased (default_tv defv)) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (RS.prel_default r defv pm x' x) as (RS.prel_default r defv pm None x);
      default_none_elim r defv pm x;
      rewrite (RS.prel_default r defv pm None x) as (RS.prel_default r defv pm x' x);
      W.r2l_post_empty (SZ.v p) v;
      true
    }
    Some a -> {
      rewrite (RS.prel_default r defv pm x' x) as (RS.prel_default r defv pm (Some a) x);
      let b = default_some_elim r defv pm a x;
      let res = w a #b out pos;
      rewrite (r pm a b) as (RS.prel_default r defv pm x' x);
      res
    }
  }
}

(* Pairs: the second component is written first *)

inline_for_extraction
fn write_pair (#t1 #t2: Type0) (#u1 #u2: Type0) (r1: prel t1 u1) (r2: prel t2 u2)
  (#enc1: u1 -> GTot SB.bytes) (#enc2: u2 -> GTot SB.bytes) (pm: perm)
  (w1: W.r2l_writer_f (r1 pm) enc1) (w2: W.r2l_writer_f (r2 pm) enc2)
: W.r2l_writer_f #(t1 & t2) #(u1 & u2) (prel_pair r1 r2 pm) (WLm.pair_enc enc1 enc2)
= (x': t1 & t2) (#x: Ghost.erased (u1 & u2)) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (prel_pair r1 r2 pm x' x);
  let ok = w2 (snd x') #(snd x) out pos;
  if ok {
    with v1 p1 . assert (pts_to out v1 ** R.pts_to pos p1);
    let res = w1 (fst x') #(fst x) out pos;
    with v2 p2 . assert (pts_to out v2 ** R.pts_to pos p2);
    W.r2l_post_append (enc1 (fst x)) (enc2 (snd x)) (SZ.v p) v (SZ.v p1) v1 res (SZ.v p2) v2;
    fold (prel_pair r1 r2 pm x' x);
    res
  } else {
    fold (prel_pair r1 r2 pm x' x);
    false
  }
}

(* ANY: the value is already serialized *)

inline_for_extraction
fn write_slice_ser (#u: Type0) (enc: u -> GTot SB.bytes) (pm: perm)
: W.r2l_writer_f #(S.slice U8.t) #u (prel_slice_ser enc pm) enc
= (x': S.slice U8.t) (#x: Ghost.erased u) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (prel_slice_ser enc pm x' x);
  with w . assert (S.pts_to x' #pm w);
  fold (W.vmatch_bytes pm x' w);
  let res = W.r2l_write_copy pm x' #w out pos;
  unfold (W.vmatch_bytes pm x' w);
  fold (prel_slice_ser enc pm x' x);
  res
}

(* Restricted terminals *)

inline_for_extraction
fn write_restricted (id: asn1_id_t) (k: asn1_terminal_k) (r: asn1_restriction k) (pm: perm)
  (wt: W.r2l_writer_f (asn1_terminal_rel k pm) (WL.terminal_enc id k))
: W.r2l_writer_f #(asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) #(asn1_content_t (ASN1_RESTRICTED_TERMINAL k r))
    (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm) (WLm.cenc id (ASN1_RESTRICTED_TERMINAL k r))
= (x': asn1_content_impl_t (ASN1_RESTRICTED_TERMINAL k r)) (#x: Ghost.erased (asn1_content_t (ASN1_RESTRICTED_TERMINAL k r)))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  RS.content_restricted_eq k r pm x' x;
  rewrite (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm x' x) as (asn1_terminal_rel k pm x' (RS.restricted_up k r x));
  let res = wt x' #(RS.restricted_up k r x) out pos;
  rewrite (asn1_terminal_rel k pm x' (RS.restricted_up k r x)) as (asn1_content_rel (ASN1_RESTRICTED_TERMINAL k r) pm x' x);
  WLm.cenc_restricted id k r x;
  res
}

(* CHOICE alternatives *)

ghost
fn lc_single_elim (id': asn1_id_t) (c: asn1_content_k) (pm: perm) (x: asn1_lc_impl_t [(id', c)]) (v: make_gen_choice_type (asn1_lc_t [(id', c)]))
requires asn1_lc_rel [(id', c)] pm x v
returns b: Ghost.erased (asn1_content_t c)
ensures asn1_content_rel c pm x b ** Trade.trade (asn1_content_rel c pm x b) (asn1_lc_rel [(id', c)] pm x v) **
  pure (WLm.lcenc [(id', c)] v == WLm.cenc id' c b)
{
  RS.lc_single_eq id' c pm x v;
  if (dfst v = id') {
    WLm.lcenc_head id' c [] v;
    let b : Ghost.erased (asn1_content_t c) = Ghost.hide (RS.lc_head_val id' c [] v ());
    Trade.rewrite_with_trade (asn1_lc_rel [(id', c)] pm x v) (asn1_content_rel c pm x b);
    b
  } else {
    rewrite (asn1_lc_rel [(id', c)] pm x v) as (pure False);
    unreachable ()
  }
}

ghost
fn lc_cons_inl_elim (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (x: asn1_lc_impl_t ((id', c) :: hd2 :: tl2)) (a: asn1_content_impl_t c)
  (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
requires asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x v ** pure (x == RS.lc_inl id' c hd2 tl2 a)
returns b: Ghost.erased (asn1_content_t c)
ensures asn1_content_rel c pm a b ** Trade.trade (asn1_content_rel c pm a b) (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x v) **
  pure (WLm.lcenc ((id', c) :: hd2 :: tl2) v == WLm.cenc id' c b)
{
  RS.lc_cons_inl_eq id' c hd2 tl2 pm a v;
  if (dfst v = id') {
    WLm.lcenc_head id' c (hd2 :: tl2) v;
    let b : Ghost.erased (asn1_content_t c) = Ghost.hide (RS.lc_head_val id' c (hd2 :: tl2) v ());
    Trade.rewrite_with_trade (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x v) (asn1_content_rel c pm a b);
    b
  } else {
    rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x v) as (pure False);
    unreachable ()
  }
}

ghost
fn lc_cons_inr_elim (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k))
  (pm: perm) (x: asn1_lc_impl_t ((id', c) :: hd2 :: tl2)) (bi: asn1_lc_impl_t (hd2 :: tl2))
  (v: make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))
requires asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x v ** pure (x == RS.lc_inr id' c hd2 tl2 bi)
returns b: Ghost.erased (make_gen_choice_type (asn1_lc_t (hd2 :: tl2)))
ensures asn1_lc_rel (hd2 :: tl2) pm bi b ** Trade.trade (asn1_lc_rel (hd2 :: tl2) pm bi b) (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x v) **
  pure (WLm.lcenc ((id', c) :: hd2 :: tl2) v == WLm.lcenc (hd2 :: tl2) b)
{
  RS.lc_cons_inr_eq id' c hd2 tl2 pm bi v;
  if (dfst v = id') {
    rewrite (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x v) as (pure False);
    unreachable ()
  } else {
    WLm.lcenc_tail (id', c) (hd2 :: tl2) v;
    let b : Ghost.erased (make_gen_choice_type (asn1_lc_t (hd2 :: tl2))) = Ghost.hide (RS.lc_tail_val (id', c) (hd2 :: tl2) v ());
    Trade.rewrite_with_trade (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm x v) (asn1_lc_rel (hd2 :: tl2) pm bi b);
    b
  }
}

inline_for_extraction
fn write_lc_nil (pm: perm)
: W.r2l_writer_f #(asn1_lc_impl_t []) #(make_gen_choice_type (asn1_lc_t [])) (asn1_lc_rel [] pm) (WLm.lcenc [])
= (x': asn1_lc_impl_t []) (#x: Ghost.erased (make_gen_choice_type (asn1_lc_t []))) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  rewrite (asn1_lc_rel [] pm x' x) as (pure False);
  unreachable ()
}

inline_for_extraction
fn write_lc_single (id': asn1_id_t) (c: asn1_content_k) (pm: perm)
  (wc: W.r2l_writer_f (asn1_content_rel c pm) (WLm.cenc id' c))
: W.r2l_writer_f #(asn1_lc_impl_t [(id', c)]) #(make_gen_choice_type (asn1_lc_t [(id', c)])) (asn1_lc_rel [(id', c)] pm) (WLm.lcenc [(id', c)])
= (x': asn1_lc_impl_t [(id', c)]) (#x: Ghost.erased (make_gen_choice_type (asn1_lc_t [(id', c)]))) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let b = lc_single_elim id' c pm x' x;
  let res = wc x' #b out pos;
  Trade.elim _ _;
  res
}

inline_for_extraction
fn write_lc_cons (id': asn1_id_t) (c: asn1_content_k) (hd2: asn1_id_t & asn1_content_k) (tl2: list (asn1_id_t & asn1_content_k)) (pm: perm)
  (wc: W.r2l_writer_f (asn1_content_rel c pm) (WLm.cenc id' c))
  (wt: W.r2l_writer_f (asn1_lc_rel (hd2 :: tl2) pm) (WLm.lcenc (hd2 :: tl2)))
: W.r2l_writer_f #(asn1_lc_impl_t ((id', c) :: hd2 :: tl2)) #(make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2))) (asn1_lc_rel ((id', c) :: hd2 :: tl2) pm) (WLm.lcenc ((id', c) :: hd2 :: tl2))
= (x': asn1_lc_impl_t ((id', c) :: hd2 :: tl2)) (#x: Ghost.erased (make_gen_choice_type (asn1_lc_t ((id', c) :: hd2 :: tl2)))) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let x2 : either (asn1_content_impl_t c) (asn1_lc_impl_t (hd2 :: tl2)) = x';
  match x2 {
    Inl a -> {
      assert (pure (x' == RS.lc_inl id' c hd2 tl2 a));
      let b = lc_cons_inl_elim id' c hd2 tl2 pm x' a x;
      let res = wc a #b out pos;
      Trade.elim _ _;
      res
    }
    Inr bi -> {
      assert (pure (x' == RS.lc_inr id' c hd2 tl2 bi));
      let b = lc_cons_inr_elim id' c hd2 tl2 pm x' bi x;
      let res = wt bi #b out pos;
      Trade.elim _ _;
      res
    }
  }
}

(* A generic jumper over TLV elements: the identifier and the length header
   give the size of the element *)

inline_for_extraction
fn jump_k (#s: Ghost.erased (Set.set asn1_id_t)) (k: Ghost.erased (asn1_k s))
: LPS.jumper #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k)
= (input: S.slice U8.t) (offset: SZ.t) (#pm: perm) (#v: Ghost.erased SB.bytes)
{
  S.pts_to_len input;
  PSO.tlv_consumed k (Seq.slice v (SZ.v offset) (Seq.length v));
  PSO.tlv_parts v (SZ.v offset);
  let mut poff = offset;
  let oid = I.vread_identifier input poff;
  match oid {
    Some id -> {
      let off1 = !poff;
      assert (pure (match SB.parse parse_asn1_identifier_U32 (Seq.slice v (SZ.v offset) (Seq.length v)) with Some (_, c) -> SZ.v off1 == SZ.v offset + c | None -> False));
      let ol = ILC.vread_length input poff;
      match ol {
        Some l -> {
          let off2 = !poff;
          assert (pure (match SB.parse (LowParse.Spec.DER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice v (SZ.v off1) (Seq.length v)) with Some (len', c2) -> (len' <: U32.t) == l /\ SZ.v off2 == SZ.v off1 + c2 | None -> False));
          PSO.tlv_size_at v (SZ.v offset) (SZ.v off1) (SZ.v off2) l;
          SZ.fits_lte (SZ.v off2 + U32.v l) (Seq.length v);
          SZ.add off2 (SZ.uint32_to_sizet l)
        }
        None -> {
          unreachable ()
        }
      }
    }
    None -> {
      unreachable ()
    }
  }
}

(* SEQUENCE OF and SET OF: a TLV around the mixed-list writer *)

let kenc_consumed (#s: _) (k: asn1_k s) (sq: squash (Conf.wf k)) (w: SB.bytes) (y: asn1_t k)
: Lemma (requires PPB.pts_to_parsed_prop #asn1_strong_parser_kind (asn1_as_parser k) w y) (ensures WLm.kenc k y == w)
= Ser.asn1_as_parser_consumed #s k w;
  assert (Seq.equal (Seq.slice w 0 (Seq.length w)) w)

let kenc_ok (#s: _) (k: asn1_k s) (sq: squash (Conf.wf k)) : WI.enc_consumed #asn1_strong_parser_kind (asn1_as_parser k) (WLm.kenc k) =
  kenc_consumed k sq

inline_for_extraction
fn write_seq_of (id: asn1_id_t) (ne: bool) (#s: _) (k: asn1_k s)
  (u: squash (asn1_any_id_valid id /\ CONSTRUCTED? id.f /\ Conf.wf k))
  (w: (pm: perm) -> W.r2l_writer_f (asn1_rel k pm) (WLm.kenc k))
  (sh: RS.share_t (asn1_rel k)) (g: RS.gather_t (asn1_rel k))
  (pm: perm)
: W.r2l_writer_f #(asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) #(asn1_content_t (ASN1_SEQUENCE_OF ne k))
    (asn1_content_rel (ASN1_SEQUENCE_OF ne k) pm) (WLm.cenc id (ASN1_SEQUENCE_OF ne k))
= (x': asn1_content_impl_t (ASN1_SEQUENCE_OF ne k)) (#x: Ghost.erased (asn1_content_t (ASN1_SEQUENCE_OF ne k)))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  RS.seq_of_eq ne k pm x' x;
  let ml : ml (asn1_impl_t k) = x';
  rewrite (asn1_content_rel (ASN1_SEQUENCE_OF ne k) pm x' x)
    as (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm ml (RS.seq_of_up ne k x));
  let res = WL.r2l_write_tlv id
    (WI.r2l_write_mixed_list_gen (asn1_rel k) ml_ops (WLm.kenc k) (kenc_ok k ()) (jump_k k) w sh g pm)
    ml #(RS.seq_of_up ne k x) out pos;
  rewrite (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm ml (RS.seq_of_up ne k x))
    as (asn1_content_rel (ASN1_SEQUENCE_OF ne k) pm x' x);
  WLm.cenc_seq_of id ne k x;
  res
}

inline_for_extraction
fn write_set_of (id: asn1_id_t) (ne: bool) (#s: _) (k: asn1_k s)
  (u: squash (asn1_any_id_valid id /\ CONSTRUCTED? id.f /\ Conf.wf k))
  (w: (pm: perm) -> W.r2l_writer_f (asn1_rel k pm) (WLm.kenc k))
  (sh: RS.share_t (asn1_rel k)) (g: RS.gather_t (asn1_rel k))
  (pm: perm)
: W.r2l_writer_f #(asn1_content_impl_t (ASN1_SET_OF ne k)) #(asn1_content_t (ASN1_SET_OF ne k))
    (asn1_content_rel (ASN1_SET_OF ne k) pm) (WLm.cenc id (ASN1_SET_OF ne k))
= (x': asn1_content_impl_t (ASN1_SET_OF ne k)) (#x: Ghost.erased (asn1_content_t (ASN1_SET_OF ne k)))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  RS.set_of_eq ne k pm x' x;
  let ml : ml (asn1_impl_t k) = x';
  rewrite (asn1_content_rel (ASN1_SET_OF ne k) pm x' x)
    as (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm ml (RS.set_of_up ne k x));
  let res = WL.r2l_write_tlv id
    (WI.r2l_write_mixed_list_gen (asn1_rel k) ml_ops (WLm.kenc k) (kenc_ok k ()) (jump_k k) w sh g pm)
    ml #(RS.set_of_up ne k x) out pos;
  rewrite (It.mixed_list_match (asn1_rel k) ml_ops #asn1_strong_parser_kind (asn1_as_parser k) pm ml (RS.set_of_up ne k x))
    as (asn1_content_rel (ASN1_SET_OF ne k) pm x' x);
  WLm.cenc_set_of id ne k x;
  res
}
