module ASN1.Pulse.RawWriter
#lang-pulse

(* Raw right-to-left writers.

   The raw writer `raw_write_k k` writes the bytes `w` of a raw Pulse
   representation `x` (`ASN1.Pulse.RawRel.raw_rel k pm x w`), with no
   semantic precondition on `x`: any slice, any integer, any number of
   unused bits, any DEFAULT component, etc. It is used by the JIT writer
   (`ASN1.Pulse.JitWriter`) to write again, then validate, the contents
   whose validity it could not check while writing them. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Content.Enc
open ASN1.Spec.Value.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.RawRel

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module I64 = FStar.Int64
module R = Pulse.Lib.Reference
module SB = LowParse.Spec.Base
module SC = LowParse.Spec.Combinators
module LPS = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators
module It = LowParse.PulseParse.Iterator
module WI = LowParse.PulseParse.Iterator.R2L
module W = LowParse.Pulse.R2L
module WL = ASN1.Pulse.WriteLeaf
module WC = ASN1.Pulse.WriteComb
module RS = ASN1.Pulse.RelShare
module PS = ASN1.Pulse.ParseSequence
module Conf = ASN1.Spec.Conformance
module In = ASN1.Pulse.Interpreter
module SI = ASN1.Pulse.SortedInsert
module WA = ASN1.Pulse.WriteAdb
module PA = ASN1.Pulse.ParseAdb
module DE = ASN1.Pulse.DefaultEq

inline_for_extraction
let rw (#t: Type0) (r: bprel t) (pm: perm) = W.r2l_writer_f #t #SB.bytes (r pm) id_enc

(* Combinators *)

inline_for_extraction
let raw_write_ext (#t: Type0) (r1 r2: bprel t) (sq: squash (prel_equiv r1 r2)) (pm: perm) (w: rw r1 pm) : rw r2 pm =
  WC.write_ext r1 r2 sq id_enc (fun _ -> ()) pm w

inline_for_extraction
fn raw_write_tlv (id: asn1_id_t) (#t: Type0) (r: bprel t) (pm: perm) (w: rw r pm)
: rw #t (raw_tlv id r) pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_tlv id r pm x' x);
  with c . assert (r pm x' c);
  let res = WL.r2l_write_tlv id w x' #c out pos;
  fold (raw_tlv id r pm x' x);
  res
}

inline_for_extraction
fn raw_write_cat (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm) (w1: rw r1 pm) (w2: rw r2 pm)
: rw #(t1 & t2) (raw_cat r1 r2) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_cat r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  let ok = w2 (snd x') #c2 out pos;
  if ok {
    with v1 p1 . assert (pts_to out v1 ** R.pts_to pos p1);
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (pts_to out v2 ** R.pts_to pos p2);
    W.r2l_post_append c1 c2 (SZ.v p) v (SZ.v p1) v1 res (SZ.v p2) v2;
    fold (raw_cat r1 r2 pm x' x);
    res
  } else {
    W.r2l_post_false_weaken c2 x (SZ.v p) v (SZ.v p) v;
    fold (raw_cat r1 r2 pm x' x);
    false
  }
}

(* Write `x`, then the constant `e` to its left *)
inline_for_extraction
fn raw_write_pre (e: SB.bytes) (cw: WA.cwriter e) (#t: Type0) (r: bprel t) (pm: perm) (w: rw r pm)
: rw #t (raw_pre e r) pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_pre e r pm x' x);
  with c . assert (r pm x' c);
  let res = WA.write_then_const w cw x' #c out pos;
  fold (raw_pre e r pm x' x);
  res
}

(* Write `snd x`, then `fst x`, then insert the latter at its sorted
   position into the former *)
inline_for_extraction
fn raw_write_ins (lt: SI.lt_t) (lt_impl: SI.lt_impl_t lt) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm) (w1: rw r1 pm) (w2: rw r2 pm)
: rw #(t1 & t2) (raw_ins lt r1 r2) pm
= (x': t1 & t2) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_ins lt r1 r2 pm x' x);
  with c1 c2 . assert (r1 pm (fst x') c1 ** r2 pm (snd x') c2);
  let p0 = !pos;
  let ok = w2 (snd x') #c2 out pos;
  if ok {
    with v1 p1 . assert (pts_to out v1 ** R.pts_to pos p1);
    let p1r = !pos;
    let res = w1 (fst x') #c1 out pos;
    with v2 p2 . assert (pts_to out v2 ** R.pts_to pos p2);
    if res {
      let p2r = !pos;
      SI.r2l_insert lt lt_impl out p2r p1r p0;
      with v3 . assert (pts_to out v3);
      SI.r2l_post_ins lt c1 c2 (SZ.v p) v (SZ.v p1) v1 (SZ.v p2) v2 v3;
      fold (raw_ins lt r1 r2 pm x' x);
      true
    } else {
      W.r2l_post_append c1 c2 (SZ.v p) v (SZ.v p1) v1 res (SZ.v p2) v2;
      SI.ins_length lt c1 c2;
      W.r2l_post_false_weaken (Seq.append c1 c2) x (SZ.v p) v (SZ.v p2) v2;
      fold (raw_ins lt r1 r2 pm x' x);
      false
    }
  } else {
    SI.ins_length lt c1 c2;
    W.r2l_post_false_weaken c2 x (SZ.v p) v (SZ.v p) v;
    fold (raw_ins lt r1 r2 pm x' x);
    false
  }
}

inline_for_extraction
let raw_write_join (srt: bool) (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm) (w1: rw r1 pm) (w2: rw r2 pm)
: rw (raw_join srt r1 r2) pm
= if srt
  then (join_ins_equiv srt r1 r2; raw_write_ext (raw_ins SI.lt_tag r1 r2) (raw_join srt r1 r2) () pm (raw_write_ins SI.lt_tag (SI.lt_tag_impl ()) r1 r2 pm w1 w2))
  else (join_cat_equiv srt r1 r2; raw_write_ext (raw_cat r1 r2) (raw_join srt r1 r2) () pm (raw_write_cat r1 r2 pm w1 w2))

inline_for_extraction
fn raw_write_opt (#t: Type0) (r: bprel t) (pm: perm) (w: rw r pm)
: rw #(option t) (raw_opt r) pm
= (x': option t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (raw_opt r pm x' x) as (pure (Ghost.reveal x == Seq.empty));
      W.r2l_post_empty (SZ.v p) v;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt r pm x' x);
      true
    }
    Some a -> {
      rewrite (raw_opt r pm x' x) as (r pm a x);
      let res = w a #x out pos;
      rewrite (r pm a x) as (raw_opt r pm x' x);
      res
    }
  }
}

(* An explicit default value is not written *)
inline_for_extraction
fn raw_write_opt_nd (d: SB.bytes) (#t: Type0) (r: bprel t) (pm: perm) (dec: DE.dd r d pm) (w: rw r pm)
: rw #(option t) (raw_opt_nd d r) pm
= (x': option t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    None -> {
      rewrite (raw_opt_nd d r pm x' x) as (pure (Ghost.reveal x == Seq.empty));
      W.r2l_post_empty (SZ.v p) v;
      rewrite (pure (Ghost.reveal x == Seq.empty)) as (raw_opt_nd d r pm x' x);
      true
    }
    Some a -> {
      rewrite (raw_opt_nd d r pm x' x) as (raw_opt_nd d r pm (Some a) x);
      unfold (raw_opt_nd d r pm (Some a) x);
      with c . assert (r pm a c);
      let isd = dec a #c;
      if isd {
        W.r2l_post_empty (SZ.v p) v;
        fold (raw_opt_nd d r pm (Some a) x);
        rewrite (raw_opt_nd d r pm (Some a) x) as (raw_opt_nd d r pm x' x);
        true
      } else {
        rewrite (r pm a c) as (r pm a x);
        let res = w a #x out pos;
        rewrite (r pm a x) as (r pm a c);
        fold (raw_opt_nd d r pm (Some a) x);
        rewrite (raw_opt_nd d r pm (Some a) x) as (raw_opt_nd d r pm x' x);
        res
      }
    }
  }
}

inline_for_extraction
fn raw_write_either (#t1 #t2: Type0) (r1: bprel t1) (r2: bprel t2) (pm: perm) (w1: rw r1 pm) (w2: rw r2 pm)
: rw #(either t1 t2) (raw_either r1 r2) pm
= (x': either t1 t2) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    Inl a -> {
      rewrite (raw_either r1 r2 pm x' x) as (r1 pm a x);
      let res = w1 a #x out pos;
      rewrite (r1 pm a x) as (raw_either r1 r2 pm x' x);
      res
    }
    Inr b -> {
      rewrite (raw_either r1 r2 pm x' x) as (r2 pm b x);
      let res = w2 b #x out pos;
      rewrite (r2 pm b x) as (raw_either r1 r2 pm x' x);
      res
    }
  }
}

inline_for_extraction
fn raw_write_false (t: Type0) (pm: perm)
: rw #t (raw_false t) pm
= (x': t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_false t pm x' x);
  unreachable ()
}

inline_for_extraction
let raw_write_slice (pm: perm) : rw raw_slice pm =
  WC.write_slice_ser id_enc pm

(* Mixed lists, whose serialized chunks are sequences of TLVs *)

let p_raw_eq (_: unit) : Lemma (any_enc_injective (); p_raw == SC.parse_synth p_any any_enc) = ()

inline_for_extraction
let jump_raw : LPS.jumper p_raw =
  any_enc_injective ();
  p_raw_eq ();
  LPC.jump_synth #asn1_value #SB.bytes #asn1_strong_parser_kind #p_any (WC.jump_k ASN1_ANY_ILC) any_enc

inline_for_extraction
fn raw_write_ml (#t: Type0) (r: bprel t) (w: (pm: perm) -> rw r pm) (sh: share_t r) (g: gather_t r) (pm: perm)
: rw #(ml t) (raw_ml r) pm
= (x': ml t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_ml r pm x' x);
  with l . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw pm x' l);
  let res = WI.r2l_write_mixed_list_gen r ml_ops #asn1_strong_parser_kind #p_raw id_enc p_raw_consumed jump_raw w sh g pm x' #l out pos;
  fold (raw_ml r pm x' x);
  res
}

inline_for_extraction
fn raw_write_ml_sorted (#t: Type0) (r: bprel t) (w: (pm: perm) -> rw r pm) (sh: share_t r) (g: gather_t r) (pm: perm)
: rw #(ml t) (raw_ml_sorted r) pm
= (x': ml t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_ml_sorted r pm x' x);
  with l . assert (It.mixed_list_match r ml_ops #asn1_strong_parser_kind p_raw pm x' l);
  let res = SI.r2l_write_mixed_list_sorted_gen r ml_ops #asn1_strong_parser_kind #p_raw id_enc p_raw_consumed jump_raw w sh g SI.lt_lex (SI.lt_lex_impl ()) pm x' #l out pos;
  fold (raw_ml_sorted r pm x' x);
  res
}

(* Leaves *)

inline_for_extraction
fn raw_write_boolean (pm: perm)
: rw #bool (raw_pure boolean_enc) pm
= (x': bool) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_pure boolean_enc pm x' x);
  fold (prel_eq bool pm x' x');
  let res = WL.r2l_write_boolean pm x' #x' out pos;
  unfold (prel_eq bool pm x' x');
  fold (raw_pure boolean_enc pm x' x);
  res
}

inline_for_extraction
fn raw_write_null (pm: perm)
: rw #unit (raw_pure null_enc) pm
= (x': unit) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_pure null_enc pm x' x);
  W.r2l_post_empty (SZ.v p) v;
  fold (raw_pure null_enc pm x' x);
  true
}

inline_for_extraction
fn raw_write_i64 (pm: perm)
: rw #I64.t raw_i64 pm
= (x': I64.t) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_i64 pm x' x);
  unfold (raw_pure i64_enc pm x' x);
  let res = WL.r2l_write_i64 8 x' (i64_int x') out pos;
  fold (raw_pure i64_enc pm x' x);
  fold (raw_i64 pm x' x);
  res
}

inline_for_extraction
fn raw_write_int (pm: perm)
: rw #asn1_int_impl raw_int pm
= (x': asn1_int_impl) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  match x' {
    Small i -> {
      rewrite (raw_int pm x' x) as (pure (Ghost.reveal x == i64_enc i));
      let res = WL.r2l_write_i64 8 i (i64_int i) out pos;
      rewrite (pure (Ghost.reveal x == i64_enc i)) as (raw_int pm x' x);
      res
    }
    Big s -> {
      rewrite (raw_int pm x' x) as (raw_slice pm s x);
      let res = raw_write_slice pm s #x out pos;
      rewrite (raw_slice pm s x) as (raw_int pm x' x);
      res
    }
  }
}

inline_for_extraction
fn raw_write_bitstring (pm: perm)
: rw #asn1_bitstring_impl raw_bitstring pm
= (x': asn1_bitstring_impl) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_bitstring pm x' x);
  with w . assert (S.pts_to x'.bytes #pm w);
  fold (W.vmatch_bytes pm x'.bytes w);
  let res = W.r2l_write_copy pm x'.bytes #w out pos;
  unfold (W.vmatch_bytes pm x'.bytes w);
  if (res) {
    with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
    let u = x'.unused;
    fold (LPS.eq_as_slprop U8.t u u);
    let res' = W.r2l_write_byte () u out pos;
    unfold (LPS.eq_as_slprop U8.t u u);
    with v2 p2 . assert (pts_to out v2 ** pts_to pos p2);
    W.r2l_post_append (W.enc_byte u) w (SZ.v p) v (SZ.v p1) v1 res' (SZ.v p2) v2;
    fold (raw_bitstring pm x' x);
    res'
  } else {
    W.r2l_post_false_weaken w x (SZ.v p) v (SZ.v p) v;
    fold (raw_bitstring pm x' x);
    false
  }
}

[@@In.asn1_pulse_attr]
inline_for_extraction
let raw_write_integer (bound: pos) (pm: perm) : rw (raw_integer bound) pm =
  if small_integer bound
  then coerce_eq () (raw_write_i64 pm)
  else coerce_eq () (raw_write_int pm)

[@@In.asn1_pulse_attr]
inline_for_extraction
let raw_write_leaf (k: leaf_k) (pm: perm) : rw (raw_leaf k) pm =
  match k with
  | ASN1_BOOLEAN -> raw_write_boolean pm
  | ASN1_NULL -> raw_write_null pm
  | ASN1_INTEGER bound -> raw_write_integer bound pm
  | ASN1_BITSTRING -> raw_write_bitstring pm
  | ASN1_OCTETSTRING -> raw_write_slice pm
  | ASN1_PRINTABLESTRING -> raw_write_slice pm
  | ASN1_UTF8STRING -> raw_write_slice pm
  | ASN1_IA5STRING -> raw_write_slice pm
  | ASN1_VISIBLESTRING -> raw_write_slice pm
  | ASN1_BMPSTRING -> raw_write_slice pm
  | ASN1_UNIVERSALSTRING -> raw_write_slice pm
  | ASN1_TELETEXSTRING -> raw_write_slice pm
  | ASN1_NUMERICSTRING -> raw_write_slice pm
  | ASN1_VIDEOTEXSTRING -> raw_write_slice pm
  | ASN1_GRAPHICSTRING -> raw_write_slice pm
  | ASN1_GENERALSTRING -> raw_write_slice pm
  | ASN1_OBJECTDESCRIPTOR -> raw_write_slice pm
  | ASN1_OID -> raw_write_slice pm
  | ASN1_RELATIVE_OID -> raw_write_slice pm
  | ASN1_OID_IRI -> raw_write_slice pm
  | ASN1_RELATIVE_OID_IRI -> raw_write_slice pm
  | ASN1_UTCTIME -> raw_write_slice pm
  | ASN1_GENERALIZEDTIME -> raw_write_slice pm
  | ASN1_DATE -> raw_write_slice pm
  | ASN1_TIME_OF_DAY -> raw_write_slice pm
  | ASN1_DATE_TIME -> raw_write_slice pm

(* Terminals, with their identifier *)

inline_for_extraction
fn raw_write_terminal_prefixed (id: asn1_id_t) (id2: asn1_id_t) (k2: asn1_terminal_k) (pm: perm) (w: rw (raw_terminal_rel id2 k2) pm)
: rw #(asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2)) pm
= (x': asn1_terminal_impl_t (ASN1_PREFIXED_TERMINAL id2 k2)) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  terminal_prefixed_eq id id2 k2 pm x' x;
  let x2 = prefixed_down id2 k2 x';
  rewrite (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x' x) as (raw_tlv id (raw_terminal_rel id2 k2) pm x2 x);
  let res = raw_write_tlv id (raw_terminal_rel id2 k2) pm w x2 #x out pos;
  rewrite (raw_tlv id (raw_terminal_rel id2 k2) pm x2 x) as (raw_terminal_rel id (ASN1_PREFIXED_TERMINAL id2 k2) pm x' x);
  res
}

inline_for_extraction
let raw_write_leaf_tlv (id: asn1_id_t) (k: leaf_k) (pm: perm) : rw (raw_terminal_rel id k) pm =
  terminal_leaf_equiv id k;
  raw_write_ext (raw_tlv id (raw_leaf k)) (raw_terminal_rel id k) () pm (raw_write_tlv id (raw_leaf k) pm (raw_write_leaf k pm))

let wres (#t: Type0) (r: bprel t) (pm: perm) (x': t) (x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (v: Ghost.erased SB.bytes) (p: Ghost.erased SZ.t) : Type =
  WL.wres (r pm) id_enc x' x out pos v p

[@@In.asn1_pulse_attr]
let rec raw_write_terminal (id: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) (pm: perm)
  (x': asn1_terminal_impl_t k) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_terminal_rel id k) pm x' x out pos v p)
  (decreases k)
= [@inline_let] let vf : rw (raw_terminal_rel id k) pm =
  (match k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    raw_write_terminal_prefixed id id2 k2 pm
      (fun x' #x out pos #v #p -> raw_write_terminal id2 k2 pm x' #x out pos #v #p)
  | ASN1_BOOLEAN -> raw_write_leaf_tlv id k pm
  | ASN1_NULL -> raw_write_leaf_tlv id k pm
  | ASN1_INTEGER _ -> raw_write_leaf_tlv id k pm
  | ASN1_BITSTRING -> raw_write_leaf_tlv id k pm
  | ASN1_OCTETSTRING -> raw_write_leaf_tlv id k pm
  | ASN1_PRINTABLESTRING -> raw_write_leaf_tlv id k pm
  | ASN1_UTF8STRING -> raw_write_leaf_tlv id k pm
  | ASN1_IA5STRING -> raw_write_leaf_tlv id k pm
  | ASN1_VISIBLESTRING -> raw_write_leaf_tlv id k pm
  | ASN1_BMPSTRING -> raw_write_leaf_tlv id k pm
  | ASN1_UNIVERSALSTRING -> raw_write_leaf_tlv id k pm
  | ASN1_TELETEXSTRING -> raw_write_leaf_tlv id k pm
  | ASN1_NUMERICSTRING -> raw_write_leaf_tlv id k pm
  | ASN1_VIDEOTEXSTRING -> raw_write_leaf_tlv id k pm
  | ASN1_GRAPHICSTRING -> raw_write_leaf_tlv id k pm
  | ASN1_GENERALSTRING -> raw_write_leaf_tlv id k pm
  | ASN1_OBJECTDESCRIPTOR -> raw_write_leaf_tlv id k pm
  | ASN1_OID -> raw_write_leaf_tlv id k pm
  | ASN1_RELATIVE_OID -> raw_write_leaf_tlv id k pm
  | ASN1_OID_IRI -> raw_write_leaf_tlv id k pm
  | ASN1_RELATIVE_OID_IRI -> raw_write_leaf_tlv id k pm
  | ASN1_UTCTIME -> raw_write_leaf_tlv id k pm
  | ASN1_GENERALIZEDTIME -> raw_write_leaf_tlv id k pm
  | ASN1_DATE -> raw_write_leaf_tlv id k pm
  | ASN1_TIME_OF_DAY -> raw_write_leaf_tlv id k pm
  | ASN1_DATE_TIME -> raw_write_leaf_tlv id k pm)
  in vf x' #x out pos #v #p

[@@In.asn1_pulse_attr]
inline_for_extraction
let raw_write_default (id0: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k: asn1_terminal_k) ([@@@FStar.Attributes.monomorphize] defl: asn1_key_lit k) (pm: perm)
  (x': option (asn1_terminal_impl_t k)) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_default_rel id0 k defl) pm x' x out pos v p)
= if In.adb_key_supported k
  then begin
    default_nd_equiv id0 k defl;
    raw_write_ext (raw_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl) () pm
      (raw_write_opt_nd (WA.raw_key_enc id0 k defl) (raw_terminal_rel id0 k) pm
        (fun x' #c -> DE.dd_term id0 k defl () pm x' #c)
        (fun x' #x out pos #v #p -> raw_write_terminal id0 k pm x' #x out pos #v #p))
      x' #x out pos #v #p
  end else begin
    default_opt_equiv id0 k defl;
    raw_write_ext (raw_opt (raw_terminal_rel id0 k)) (raw_default_rel id0 k defl) () pm
      (raw_write_opt (raw_terminal_rel id0 k) pm (fun x' #x out pos #v #p -> raw_write_terminal id0 k pm x' #x out pos #v #p))
      x' #x out pos #v #p
  end

inline_for_extraction
fn raw_write_view (#t #ty: Type0) (r: bprel t) (view: ty -> t) (pm: perm) (w: rw r pm)
: rw #ty (raw_view r view) pm
= (x': ty) (#x: Ghost.erased SB.bytes) (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  unfold (raw_view r view pm x' x);
  let res = w (view x') #x out pos;
  fold (raw_view r view pm x' x);
  res
}

(* The whole schema, by descriptor *)

let rec raw_write_crel (id: asn1_id_t) (#[@@@FStar.Attributes.monomorphize] k: asn1_content_k) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: cdesc k t) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_crel id d) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : rw (raw_crel id d) pm =
  (match d with
  | CD_TERMINAL k' ->
    content_terminal_equiv id k';
    raw_write_ext (raw_terminal_rel id k') (raw_crel id d) () pm
      (fun x' #x out pos #v #p -> raw_write_terminal id k' pm x' #x out pos #v #p)
  | CD_RESTRICTED k' r ->
    content_restricted_equiv id k' r;
    raw_write_ext (raw_terminal_rel id k') (raw_crel id d) () pm
      (fun x' #x out pos #v #p -> raw_write_terminal id k' pm x' #x out pos #v #p)
  | CD_PREFIXED d' ->
    content_prefixed_equiv id d';
    raw_write_ext (raw_tlv id (raw_arel d')) (raw_crel id d) () pm
      (raw_write_tlv id (raw_arel d') pm (fun x' #x out pos #v #p -> raw_write_arel d' pm x' #x out pos #v #p))
  | CD_SEQUENCE gitems di ->
    content_sequence_equiv id gitems di;
    raw_write_ext (raw_tlv id (raw_irel false di)) (raw_crel id d) () pm
      (raw_write_tlv id (raw_irel false di) pm (fun x' #x out pos #v #p -> raw_write_irel false di pm x' #x out pos #v #p))
  | CD_SET ids items pf di ->
    content_set_equiv id ids items pf di;
    raw_write_ext (raw_tlv id (raw_irel true di)) (raw_crel id d) () pm
      (raw_write_tlv id (raw_irel true di) pm (fun x' #x out pos #v #p -> raw_write_irel true di pm x' #x out pos #v #p))
  | CD_SEQUENCE_OF ne d' ->
    content_seq_of_equiv id ne d';
    raw_write_ext (raw_tlv id (raw_ml (raw_arel d'))) (raw_crel id d) () pm
      (raw_write_tlv id (raw_ml (raw_arel d')) pm
        (raw_write_ml (raw_arel d') (fun pm x' #x out pos #v #p -> raw_write_arel d' pm x' #x out pos #v #p) (share_arel d') (gather_arel d') pm))
  | CD_SET_OF ne d' ->
    content_set_of_equiv id ne d';
    raw_write_ext (raw_tlv id (raw_ml_sorted (raw_arel d'))) (raw_crel id d) () pm
      (raw_write_tlv id (raw_ml_sorted (raw_arel d')) pm
        (raw_write_ml_sorted (raw_arel d') (fun pm x' #x out pos #v #p -> raw_write_arel d' pm x' #x out pos #v #p) (share_arel d') (gather_arel d') pm))
  | CD_ADB_NONE ipd prefix kid key_k ls pf pf' dsx dpre ->
    content_adb_none_equiv id ipd prefix kid key_k ls pf pf' dsx dpre;
    raw_write_ext (raw_tlv id (raw_iarel dpre (raw_sxrel kid dsx))) (raw_crel id d) () pm
      (raw_write_tlv id (raw_iarel dpre (raw_sxrel kid dsx)) pm (fun x' #x out pos #v #p ->
        raw_write_iarel dpre (raw_sxrel kid dsx) pm
          (fun x' #x out pos #v #p -> raw_write_sxrel kid dsx pm x' #x out pos #v #p)
          x' #x out pos #v #p))
  | CD_ADB_SOME ipd prefix kid key_k ls fb pf pf' dfb dfx dpre ->
    content_adb_some_equiv id ipd prefix kid key_k ls fb pf pf' dfb dfx dpre;
    raw_write_ext (raw_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)))) (raw_crel id d) () pm
      (raw_write_tlv id (raw_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb))) pm (fun x' #x out pos #v #p ->
        raw_write_iarel dpre (raw_fxrel kid dfx (raw_dfbr kid key_k #fb dfb)) pm
          (fun x' #x out pos #v #p -> raw_write_fxrel kid dfx (raw_dfbr kid key_k #fb dfb) pm
            (raw_write_cat (raw_terminal_rel kid key_k) (raw_irel false dfb) pm
              (fun x' #x out pos #v #p -> raw_write_terminal kid key_k pm x' #x out pos #v #p)
              (fun x' #x out pos #v #p -> raw_write_irel false dfb pm x' #x out pos #v #p))
            x' #x out pos #v #p)
          x' #x out pos #v #p))
  | CD_VIEW d' ty view mk law ->
    content_view_equiv id d' ty view mk law;
    raw_write_ext (raw_view (raw_crel id d') view) (raw_crel id d) () pm
      (raw_write_view (raw_crel id d') view pm (fun x' #x out pos #v #p -> raw_write_crel id d' pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

(* ANY DEFINED BY: the prefix items, then the suffix (written first) *)
and raw_write_iarel (#[@@@FStar.Attributes.monomorphize] i: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (#[@@@FStar.Attributes.monomorphize] sfx: Type0) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: iadesc ls sfx t)
  (sr: bprel sfx) (pm: perm) ([@@@FStar.Attributes.monomorphize] ws: rw sr pm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_iarel d sr) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : rw (raw_iarel d sr) pm =
  (match d with
  | IA_NIL ->
    items_any_nil_equiv sr;
    raw_write_ext sr (raw_iarel d sr) () pm ws
  | IA_SINGLE dd ->
    items_any_single_equiv dd sr;
    raw_write_ext (raw_cat (raw_drel dd) sr) (raw_iarel d sr) () pm
      (raw_write_cat (raw_drel dd) sr pm
        (fun x' #x out pos #v #p -> raw_write_drel dd pm x' #x out pos #v #p)
        ws)
  | IA_CONS dd dtl ->
    items_any_cons_equiv dd dtl sr;
    raw_write_ext (raw_cat (raw_drel dd) (raw_iarel dtl sr)) (raw_iarel d sr) () pm
      (raw_write_cat (raw_drel dd) (raw_iarel dtl sr) pm
        (fun x' #x out pos #v #p -> raw_write_drel dd pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> raw_write_iarel dtl sr pm ws x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and raw_write_sxrel (kid: asn1_id_t) (#[@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k)
  (#[@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: sxdesc key_k ls t) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_sxrel kid d) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : rw (raw_sxrel kid d) pm =
  (match d with
  | SX_NIL _ ->
    adb_nil_equiv kid key_k;
    raw_write_ext (raw_false unit) (raw_sxrel kid d) () pm (raw_write_false unit pm)
  | SX_SINGLE _ kx y di ->
    adb_single_equiv kid kx y di;
    raw_write_ext (raw_dlit kid kx #y di) (raw_sxrel kid d) () pm
      (raw_write_pre (WA.raw_key_enc kid key_k kx)
          (fun x' #xx out pos #v #p -> WA.cw_raw_key kid key_k kx x' #xx out pos #v #p)
          (raw_irel false di) pm
          (fun x' #x out pos #v #p -> raw_write_irel false di pm x' #x out pos #v #p))
  | SX_CONS _ kx y di dtl ->
    adb_cons_equiv kid kx y di dtl;
    raw_write_ext (raw_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl)) (raw_sxrel kid d) () pm
      (raw_write_either (raw_dlit kid kx #y di) (raw_sxrel kid dtl) pm
        (raw_write_pre (WA.raw_key_enc kid key_k kx)
          (fun x' #xx out pos #v #p -> WA.cw_raw_key kid key_k kx x' #xx out pos #v #p)
          (raw_irel false di) pm
          (fun x' #x out pos #v #p -> raw_write_irel false di pm x' #x out pos #v #p))
        (fun x' #x out pos #v #p -> raw_write_sxrel kid dtl pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

(* The same, with a fallback, whose writer is `wfb` *)
and raw_write_fxrel (kid: asn1_id_t) (#[@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k)
  (#[@@@FStar.Attributes.monomorphize] ls: list (asn1_key_lit key_k & asn1_gen_items_lk)) (#[@@@FStar.Attributes.monomorphize] fbt: Type0) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: fxdesc key_k ls fbt t)
  (fbr: bprel fbt) (pm: perm) ([@@@FStar.Attributes.monomorphize] wfb: rw fbr pm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_fxrel kid d fbr) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : rw (raw_fxrel kid d fbr) pm =
  (match d with
  | FX_NIL _ ->
    afb_nil_equiv kid key_k fbr;
    raw_write_ext fbr (raw_fxrel kid d fbr) () pm wfb
  | FX_SINGLE _ kx y di ->
    afb_single_equiv kid kx y di fbr;
    raw_write_ext (raw_either (raw_dlit kid kx #y di) fbr) (raw_fxrel kid d fbr) () pm
      (raw_write_either (raw_dlit kid kx #y di) fbr pm
        (raw_write_pre (WA.raw_key_enc kid key_k kx)
          (fun x' #xx out pos #v #p -> WA.cw_raw_key kid key_k kx x' #xx out pos #v #p)
          (raw_irel false di) pm
          (fun x' #x out pos #v #p -> raw_write_irel false di pm x' #x out pos #v #p))
        wfb)
  | FX_CONS _ kx y di dtl ->
    afb_cons_equiv kid kx y di dtl fbr;
    raw_write_ext (raw_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr)) (raw_fxrel kid d fbr) () pm
      (raw_write_either (raw_dlit kid kx #y di) (raw_fxrel kid dtl fbr) pm
        (raw_write_pre (WA.raw_key_enc kid key_k kx)
          (fun x' #xx out pos #v #p -> WA.cw_raw_key kid key_k kx x' #xx out pos #v #p)
          (raw_irel false di) pm
          (fun x' #x out pos #v #p -> raw_write_irel false di pm x' #x out pos #v #p))
        (fun x' #x out pos #v #p -> raw_write_fxrel kid dtl fbr pm wfb x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and raw_write_irel ([@@@FStar.Attributes.monomorphize] srt: bool) (#[@@@FStar.Attributes.monomorphize] i: _) (#[@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: idesc ls t) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_irel srt d) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : rw (raw_irel srt d) pm =
  (match d with
  | ID_NIL ->
    items_nil_equiv srt;
    raw_write_ext (raw_pure null_enc) (raw_irel srt d) () pm (raw_write_null pm)
  | ID_SINGLE dd ->
    items_single_equiv srt dd;
    raw_write_ext (raw_drel dd) (raw_irel srt d) () pm
      (fun x' #x out pos #v #p -> raw_write_drel dd pm x' #x out pos #v #p)
  | ID_CONS dd dtl ->
    items_cons_equiv srt dd dtl;
    raw_write_ext
      (raw_join srt (raw_drel dd) (raw_irel srt dtl))
      (raw_irel srt d) () pm
      (raw_write_join srt (raw_drel dd) (raw_irel srt dtl) pm
        (fun x' #x out pos #v #p -> raw_write_drel dd pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> raw_write_irel srt dtl pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and raw_write_drel (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] dc: _) (#[@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s dc) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: ddesc dk t) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_drel d) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : rw (raw_drel d) pm =
  (match d with
  | DD_PLAIN d' ->
    dec_plain_equiv d';
    raw_write_ext (raw_arel d') (raw_drel d) () pm
      (fun x' #x out pos #v #p -> raw_write_arel d' pm x' #x out pos #v #p)
  | DD_OPTION d' ->
    dec_option_equiv d';
    raw_write_ext (raw_opt (raw_arel d')) (raw_drel d) () pm
      (raw_write_opt (raw_arel d') pm (fun x' #x out pos #v #p -> raw_write_arel d' pm x' #x out pos #v #p))
  | DD_DEFAULT id0 #k defv ->
    dec_default_equiv id0 defv;
    raw_write_ext (raw_default_rel id0 k defv) (raw_drel d) () pm
      (fun x' #x out pos #v #p -> raw_write_default id0 k defv pm x' #x out pos #v #p)
  | DD_DEFAULT_RESTRICTED id0 #k r defv ->
    dec_default_restricted_equiv id0 r defv;
    raw_write_ext (raw_default_rel id0 k defv) (raw_drel d) () pm
      (fun x' #x out pos #v #p -> raw_write_default id0 k defv pm x' #x out pos #v #p)
  | DD_VIEW d' ty view mk law ->
    dec_view_equiv d' ty view mk law;
    raw_write_ext (raw_view (raw_drel d') view) (raw_drel d) () pm
      (raw_write_view (raw_drel d') view pm (fun x' #x out pos #v #p -> raw_write_drel d' pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and raw_write_arel (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] k: asn1_k s) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: adesc k t) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_arel d) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : rw (raw_arel d) pm =
  (match d with
  | D_ILC id cd ->
    rel_ilc_equiv id cd;
    raw_write_ext (raw_crel id cd) (raw_arel d) () pm
      (fun x' #x out pos #v #p -> raw_write_crel id cd pm x' #x out pos #v #p)
  | D_CHOICE lc pf ld ->
    rel_choice_equiv lc pf ld;
    raw_write_ext (raw_lcrel ld) (raw_arel d) () pm
      (fun x' #x out pos #v #p -> raw_write_lcrel ld pm x' #x out pos #v #p)
  | D_ANY ->
    rel_any_equiv ();
    raw_write_ext raw_slice (raw_arel d) () pm (raw_write_slice pm)
  | D_VIEW d' ty view mk law ->
    rel_view_equiv d' ty view mk law;
    raw_write_ext (raw_view (raw_arel d') view) (raw_arel d) () pm
      (raw_write_view (raw_arel d') view pm (fun x' #x out pos #v #p -> raw_write_arel d' pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and raw_write_lcrel (#[@@@FStar.Attributes.monomorphize] lc: list (asn1_id_t & asn1_content_k)) (#[@@@FStar.Attributes.monomorphize] t: Type0) ([@@@FStar.Attributes.monomorphize] d: lcdesc lc t) (pm: perm)
  (x': t) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_lcrel d) pm x' x out pos v p)
  (decreases d)
= [@inline_let] let vf : rw (raw_lcrel d) pm =
  (match d with
  | LC_NIL ->
    lc_nil_equiv ();
    raw_write_ext (raw_false unit) (raw_lcrel d) () pm (raw_write_false unit pm)
  | LC_SINGLE id' cd ->
    lc_single_equiv id' cd;
    raw_write_ext (raw_crel id' cd) (raw_lcrel d) () pm
      (fun x' #x out pos #v #p -> raw_write_crel id' cd pm x' #x out pos #v #p)
  | LC_CONS id' cd dtl ->
    lc_cons_equiv id' cd dtl;
    raw_write_ext (raw_either (raw_crel id' cd) (raw_lcrel dtl)) (raw_lcrel d) () pm
      (raw_write_either (raw_crel id' cd) (raw_lcrel dtl) pm
        (fun x' #x out pos #v #p -> raw_write_crel id' cd pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> raw_write_lcrel dtl pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

(* The legacy interpreters *)

inline_for_extraction
let raw_write_content (id: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k: asn1_content_k) (pm: perm) : rw (raw_content_rel id k) pm =
  (fun x' #x out pos #v #p -> raw_write_crel id (legacy_cdesc k) pm x' #x out pos #v #p)

inline_for_extraction
let raw_write_items ([@@@FStar.Attributes.monomorphize] srt: bool) (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (pm: perm) : rw (raw_items_rel srt ls) pm =
  (fun x' #x out pos #v #p -> raw_write_irel srt (legacy_idesc ls) pm x' #x out pos #v #p)

inline_for_extraction
let raw_write_dec (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] d: _) ([@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s d) (pm: perm) : rw (raw_dec_rel dk) pm =
  (fun x' #x out pos #v #p -> raw_write_drel (legacy_ddesc dk) pm x' #x out pos #v #p)

inline_for_extraction
let raw_write_k (#[@@@FStar.Attributes.monomorphize] s: _) ([@@@FStar.Attributes.monomorphize] k: asn1_k s) (pm: perm) : rw (raw_rel k) pm =
  (fun x' #x out pos #v #p -> raw_write_arel (legacy_adesc k) pm x' #x out pos #v #p)

(* The static requirement on `k`: the validator supports it *)

let raw_ok (#s: _) (k: asn1_k s) : prop =
  In.supported_k k /\ Conf.wf k
