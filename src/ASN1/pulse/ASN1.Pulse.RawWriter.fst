module ASN1.Pulse.RawWriter
#lang-pulse

(* Raw right-to-left writers, and checked writers that check all of their
   input at runtime.

   The raw writer `raw_write_k k` writes the bytes `w` of a raw Pulse
   representation `x` (`ASN1.Pulse.RawRel.raw_rel k pm x w`), with no
   semantic precondition on `x`: any slice, any integer, any number of
   unused bits, any DEFAULT component, etc. The checked raw writer
   `check_write_raw_k` then validates `w` against `k`, so it reports
   `CW_OK` exactly when `w` is the DER encoding of a value of `k`, and
   `CW_INVALID` otherwise. The only static requirement on `k` is that the
   validator supports it. ANY DEFINED BY has no raw representation. *)

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
module CW = ASN1.Pulse.CheckedWriter

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

(* The whole schema *)

let rec raw_write_content (id: asn1_id_t) ([@@@FStar.Attributes.monomorphize] k: asn1_content_k) (pm: perm)
  (x': asn1_content_impl_t k) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_content_rel id k) pm x' x out pos v p)
  (decreases k)
= [@inline_let] let vf : rw (raw_content_rel id k) pm =
  (match k with
  | ASN1_TERMINAL k' ->
    content_terminal_equiv id k';
    raw_write_ext (raw_terminal_rel id k') (raw_content_rel id (ASN1_TERMINAL k')) () pm
      (fun x' #x out pos #v #p -> raw_write_terminal id k' pm x' #x out pos #v #p)
  | ASN1_RESTRICTED_TERMINAL k' r ->
    content_restricted_equiv id k' r;
    raw_write_ext (raw_terminal_rel id k') (raw_content_rel id (ASN1_RESTRICTED_TERMINAL k' r)) () pm
      (fun x' #x out pos #v #p -> raw_write_terminal id k' pm x' #x out pos #v #p)
  | ASN1_PREFIXED k' ->
    content_prefixed_equiv id k';
    raw_write_ext (raw_tlv id (raw_rel k')) (raw_content_rel id (ASN1_PREFIXED k')) () pm
      (raw_write_tlv id (raw_rel k') pm (fun x' #x out pos #v #p -> raw_write_k k' pm x' #x out pos #v #p))
  | ASN1_SEQUENCE gitems ->
    content_sequence_equiv id gitems;
    raw_write_ext (raw_tlv id (raw_items_rel (dsnd gitems))) (raw_content_rel id (ASN1_SEQUENCE gitems)) () pm
      (raw_write_tlv id (raw_items_rel (dsnd gitems)) pm (fun x' #x out pos #v #p -> raw_write_items (dsnd gitems) pm x' #x out pos #v #p))
  | ASN1_SET ids items pf ->
    content_set_equiv id ids items pf;
    raw_write_ext (raw_tlv id (raw_items_rel items)) (raw_content_rel id (ASN1_SET ids items pf)) () pm
      (raw_write_tlv id (raw_items_rel items) pm (fun x' #x out pos #v #p -> raw_write_items items pm x' #x out pos #v #p))
  | ASN1_SEQUENCE_OF ne k' ->
    content_seq_of_equiv id ne k';
    raw_write_ext (raw_tlv id (raw_ml (raw_rel k'))) (raw_content_rel id (ASN1_SEQUENCE_OF ne k')) () pm
      (raw_write_tlv id (raw_ml (raw_rel k')) pm
        (raw_write_ml (raw_rel k') (fun pm x' #x out pos #v #p -> raw_write_k k' pm x' #x out pos #v #p) (share_k k') (gather_k k') pm))
  | ASN1_SET_OF ne k' ->
    content_set_of_equiv id ne k';
    raw_write_ext (raw_tlv id (raw_ml (raw_rel k'))) (raw_content_rel id (ASN1_SET_OF ne k')) () pm
      (raw_write_tlv id (raw_ml (raw_rel k')) pm
        (raw_write_ml (raw_rel k') (fun pm x' #x out pos #v #p -> raw_write_k k' pm x' #x out pos #v #p) (share_k k') (gather_k k') pm))
  | ASN1_ANY_DEFINED_BY idp prefix aid key_k ls ofb pf_wf pf_sup ->
    content_adb_equiv id idp prefix aid key_k ls ofb pf_wf pf_sup;
    raw_write_ext (raw_false _) (raw_content_rel id (ASN1_ANY_DEFINED_BY idp prefix aid key_k ls ofb pf_wf pf_sup)) () pm
      (raw_write_false _ pm))
  in vf x' #x out pos #v #p

and raw_write_items (#[@@@FStar.Attributes.monomorphize] i: _) ([@@@FStar.Attributes.monomorphize] ls: asn1_gen_items_l i) (pm: perm)
  (x': asn1_items_impl_t ls) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_items_rel ls) pm x' x out pos v p)
  (decreases ls)
= [@inline_let] let vf : rw (raw_items_rel ls) pm =
  (match ls with
  | ASN1_GEN_ITEMS_NIL ->
    items_nil_equiv ();
    raw_write_ext (raw_pure null_enc) (raw_items_rel ASN1_GEN_ITEMS_NIL) () pm (raw_write_null pm)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ ASN1_GEN_ITEMS_NIL ->
    items_single_equiv dk;
    raw_write_ext (raw_dec_rel dk) (raw_items_rel (PS.single dk)) () pm
      (fun x' #x out pos #v #p -> raw_write_dec dk pm x' #x out pos #v #p)
  | ASN1_GEN_ITEMS_CONS _ _ dk _ (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) ->
    items_cons_equiv dk dk2 tl2;
    raw_write_ext
      #(asn1_decorated_impl_t dk & asn1_items_impl_t (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2))
      (raw_cat (raw_dec_rel dk) (raw_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)))
      (raw_items_rel (PS.cons2 dk dk2 tl2)) () pm
      (raw_write_cat (raw_dec_rel dk) (raw_items_rel (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2)) pm
        (fun x' #x out pos #v #p -> raw_write_dec dk pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> raw_write_items (ASN1_GEN_ITEMS_CONS s2 d2 dk2 ids2 tl2) pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and raw_write_dec (#[@@@FStar.Attributes.monomorphize] s: _) (#[@@@FStar.Attributes.monomorphize] d: _) ([@@@FStar.Attributes.monomorphize] dk: asn1_decorated_k s d) (pm: perm)
  (x': asn1_decorated_impl_t dk) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_dec_rel dk) pm x' x out pos v p)
  (decreases dk)
= [@inline_let] let vf : rw (raw_dec_rel dk) pm =
  (match dk with
  | ASN1_PLAIN_ILC k ->
    dec_plain_equiv k;
    raw_write_ext (raw_rel k) (raw_dec_rel (ASN1_PLAIN_ILC k)) () pm
      (fun x' #x out pos #v #p -> raw_write_k k pm x' #x out pos #v #p)
  | ASN1_OPTION_ILC k ->
    dec_option_equiv k;
    raw_write_ext (raw_opt (raw_rel k)) (raw_dec_rel (ASN1_OPTION_ILC k)) () pm
      (raw_write_opt (raw_rel k) pm (fun x' #x out pos #v #p -> raw_write_k k pm x' #x out pos #v #p))
  | ASN1_DEFAULT_TERMINAL id0 #k defv ->
    dec_default_equiv id0 defv;
    raw_write_ext (raw_opt (raw_terminal_rel id0 k)) (raw_dec_rel (ASN1_DEFAULT_TERMINAL id0 #k defv)) () pm
      (raw_write_opt (raw_terminal_rel id0 k) pm (fun x' #x out pos #v #p -> raw_write_terminal id0 k pm x' #x out pos #v #p))
  | ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv ->
    dec_default_restricted_equiv id0 r defv;
    raw_write_ext (raw_opt (raw_terminal_rel id0 k)) (raw_dec_rel (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defv)) () pm
      (raw_write_opt (raw_terminal_rel id0 k) pm (fun x' #x out pos #v #p -> raw_write_terminal id0 k pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

and raw_write_k (#[@@@FStar.Attributes.monomorphize] s: _) ([@@@FStar.Attributes.monomorphize] k: asn1_k s) (pm: perm)
  (x': asn1_impl_t k) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_rel k) pm x' x out pos v p)
  (decreases k)
= [@inline_let] let vf : rw (raw_rel k) pm =
  (match k with
  | ASN1_ILC id k' ->
    rel_ilc_equiv id k';
    raw_write_ext (raw_content_rel id k') (raw_rel (ASN1_ILC id k')) () pm
      (fun x' #x out pos #v #p -> raw_write_content id k' pm x' #x out pos #v #p)
  | ASN1_CHOICE_ILC lc pf ->
    rel_choice_equiv lc pf;
    raw_write_ext (raw_lc_rel lc) (raw_rel (ASN1_CHOICE_ILC lc pf)) () pm
      (fun x' #x out pos #v #p -> raw_write_lc lc pm x' #x out pos #v #p)
  | ASN1_ANY_ILC ->
    rel_any_equiv ();
    raw_write_ext raw_slice (raw_rel ASN1_ANY_ILC) () pm (raw_write_slice pm))
  in vf x' #x out pos #v #p

and raw_write_lc ([@@@FStar.Attributes.monomorphize] lc: list (asn1_id_t & asn1_content_k)) (pm: perm)
  (x': asn1_lc_impl_t lc) (#x: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (wres (raw_lc_rel lc) pm x' x out pos v p)
  (decreases lc)
= [@inline_let] let vf : rw (raw_lc_rel lc) pm =
  (match lc with
  | [] ->
    lc_nil_equiv ();
    raw_write_ext (raw_false unit) (raw_lc_rel []) () pm (raw_write_false unit pm)
  | [(id', c)] ->
    lc_single_equiv id' c;
    raw_write_ext (raw_content_rel id' c) (raw_lc_rel [(id', c)]) () pm
      (fun x' #x out pos #v #p -> raw_write_content id' c pm x' #x out pos #v #p)
  | (id', c) :: hd2 :: tl2 ->
    lc_cons_equiv id' c hd2 tl2;
    raw_write_ext (raw_either (raw_content_rel id' c) (raw_lc_rel (hd2 :: tl2))) (raw_lc_rel ((id', c) :: hd2 :: tl2)) () pm
      (raw_write_either (raw_content_rel id' c) (raw_lc_rel (hd2 :: tl2)) pm
        (fun x' #x out pos #v #p -> raw_write_content id' c pm x' #x out pos #v #p)
        (fun x' #x out pos #v #p -> raw_write_lc (hd2 :: tl2) pm x' #x out pos #v #p)))
  in vf x' #x out pos #v #p

(* Checked raw writers: write the raw bytes, then validate them against `k` *)

let raw_ok (#s: _) (k: asn1_k s) : prop =
  In.supported_k k /\ Conf.wf k

inline_for_extraction
let raw_writer (#s: _) (k: asn1_k s) (pm: perm) : rw (raw_rel k) pm =
  fun x' #x out pos #v #p -> raw_write_k k pm x' #x out pos #v #p

inline_for_extraction
let raw_validator (#s: _) (k: asn1_k s) (u: squash (raw_ok k))
: LPS.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k)
= fun input poffset #offset #pm #v -> In.validate_k k () input poffset #offset #pm #v

(* `w` and `vf` are meant to be `raw_writer k pm` and `raw_validator k u`,
   passed by the extraction root *)
inline_for_extraction
fn check_write_raw_k (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (pm: perm)
  (w: rw (raw_rel k) pm)
  (vf: LPS.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k))
  (x': asn1_impl_t k) (#y: Ghost.erased SB.bytes)
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
requires pts_to out v ** pts_to pos p ** raw_rel k pm x' y ** pure (SZ.v p <= Seq.length v)
returns res: CW.cw_result
ensures exists* v' p' . pts_to out v' ** pts_to pos p' ** raw_rel k pm x' y **
  pure (CW.cw_post k y (SZ.v p) v res (SZ.v p') v')
{
  let p0 = !pos;
  let ok = w x' #y out pos;
  if (not ok) {
    CW.CW_NO_SPACE
  } else {
    let p1 = !pos;
    with v1 . assert (pts_to out v1);
    let mut off = p1;
    let valid = vf out off;
    let off1 = !off;
    CW.check_correct k y (SZ.v p0) p1 v1 valid off1;
    if (valid && off1 = p0) {
      CW.CW_OK
    } else {
      CW.CW_INVALID
    }
  }
}

(* The type of a checked raw writer for a schema `k`: `y` is the raw bytes
   of `x'`, and the result is `CW_OK` iff they are the DER encoding of a
   value of `k` and fit in the output *)
inline_for_extraction
let checked_raw_writer_t (#s: _) (k: asn1_k s) (pm: perm) =
  (x': asn1_impl_t k) -> (#y: Ghost.erased SB.bytes) ->
  (out: S.slice U8.t) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt CW.cw_result
    (pts_to out v ** pts_to pos p ** raw_rel k pm x' y ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** raw_rel k pm x' y **
      pure (CW.cw_post k y (SZ.v p) v res (SZ.v p') v'))
