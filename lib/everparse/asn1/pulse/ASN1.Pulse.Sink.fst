module ASN1.Pulse.Sink
#lang-pulse
(* Output sinks for the JIT writers (ASN1.Pulse.JitWriter): either a real
   output buffer (`Wet`), or none (`Dry`), in which case only the position
   (that is, the remaining budget) is updated, and the ghost contents of
   the output are those that would have been written. A JIT writer run on
   a `Dry` sink thus computes the size of the encoding, and checks its
   validity, in one pass, with the same code and proofs as when writing.

   In-place operations on the output (sorted insertion for SET and SET OF,
   reversal for SEQUENCE OF) are size-neutral: on a `Dry` sink they only
   update the ghost contents. *)
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.IdentifierU32.Enc
open ASN1.Spec.Value.Enc
open ASN1.Spec.Content.Enc
open ASN1.Pulse.Rel
open ASN1.Pulse.RawRel

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module I64 = FStar.Int64
module Cast = FStar.Int.Cast
module SB = LowParse.Spec.Base
module W = LowParse.Pulse.R2L
module WL = ASN1.Pulse.WriteLeaf
module WA = ASN1.Pulse.WriteAdb
module JK = ASN1.Pulse.JitAdbKey
module RW = ASN1.Pulse.RawWriter
module In = ASN1.Pulse.Interpreter
module CE = ASN1.Spec.Content.Enc
module SI = ASN1.Pulse.SortedInsert
module WI = LowParse.PulseParse.Iterator.R2L
module DER = LowParse.Pulse.DER
module SDER = LowParse.Spec.DER
module LPB = LowParse.Spec.BoundedInt
module INT = ASN1.Spec.Content.INTEGER

noeq
type sink =
| Dry : sink
| Wet : (s: S.slice U8.t) -> sink

let sbuf (out: sink) (v: SB.bytes) : slprop =
  match out with
  | Dry -> emp
  | Wet s -> pts_to s v

ghost
fn sbuf_wet_elim (out: sink) (s: S.slice U8.t) (#v: SB.bytes)
requires sbuf out v ** pure (out == Wet s)
ensures pts_to s v
{
  rewrite (sbuf out v) as (pts_to s v)
}

ghost
fn sbuf_wet_intro (out: sink) (s: S.slice U8.t) (#v: SB.bytes)
requires pts_to s v ** pure (out == Wet s)
ensures sbuf out v
{
  rewrite (pts_to s v) as (sbuf out v)
}

ghost
fn sbuf_dry_change (out: sink) (v v': SB.bytes)
requires sbuf out v ** pure (Dry? out)
ensures sbuf out v'
{
  rewrite (sbuf out v) as emp;
  rewrite emp as (sbuf out v')
}

(* Dry writes: subtract the size from the position *)

let dry_post (e: SB.bytes) (p: nat) (res: bool) (p': nat) : prop =
  (res == true <==> Seq.length e <= p) /\
  (res == true ==> p' + Seq.length e == p)

let dry_v (e: SB.bytes) (p: nat) (v: SB.bytes) (res: bool) (p': nat) : GTot SB.bytes =
  if res && p' + Seq.length e = p && p <= Seq.length v
  then Seq.append (Seq.slice v 0 p') (Seq.append e (Seq.slice v p (Seq.length v)))
  else v

let dry_v_post (e: SB.bytes) (p: nat) (v: SB.bytes) (res: bool) (p': nat)
: Lemma (requires (dry_post e p res p' /\ p <= Seq.length v))
  (ensures (W.r2l_post e p v res p' (dry_v e p v res p')))
= if res then begin
    let v' = dry_v e p v res p' in
    assert (Seq.equal (Seq.slice v' p (Seq.length v)) (Seq.slice v p (Seq.length v)));
    assert (Seq.equal (Seq.slice v' p' p) e)
  end

inline_for_extraction
fn dry_sub (n: SZ.t) (e: Ghost.erased SB.bytes) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
requires pts_to pos p ** pure (SZ.v n == Seq.length e)
returns res: bool
ensures exists* p' . pts_to pos p' ** pure (dry_post e (SZ.v p) res (SZ.v p'))
{
  let p0 = !pos;
  if (SZ.lte n p0) {
    pos := SZ.sub p0 n;
    true
  } else {
    false
  }
}

ghost
fn dry_finish (out: sink) (e: SB.bytes) (#v: SB.bytes) (#p: SZ.t) (res: bool) (pos: ref SZ.t)
requires sbuf out v ** (exists* p' . pts_to pos p' ** pure (dry_post e (SZ.v p) res (SZ.v p'))) ** pure (Dry? out /\ SZ.v p <= Seq.length v)
ensures exists* v' p' . sbuf out v' ** pts_to pos p' ** pure (W.r2l_post e (SZ.v p) v res (SZ.v p') v')
{
  with p' . assert (pts_to pos p');
  dry_v_post e (SZ.v p) v res (SZ.v p');
  sbuf_dry_change out v (dry_v e (SZ.v p) v res (SZ.v p'))
}

(* Sink writers *)

inline_for_extraction
let swf (#t' #t: Type0) (vmatch: t' -> t -> slprop) (enc: t -> GTot SB.bytes) =
  (x': t') -> (#x: Ghost.erased t) ->
  (out: sink) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt bool
    (sbuf out v ** pts_to pos p ** vmatch x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . sbuf out v' ** pts_to pos p' ** vmatch x' x **
       pure (W.r2l_post (enc x) (SZ.v p) v res (SZ.v p') v'))

(* Dry writers: only the position *)
inline_for_extraction
let dwf (#t' #t: Type0) (vmatch: t' -> t -> slprop) (enc: t -> GTot SB.bytes) =
  (x': t') -> (#x: Ghost.erased t) -> (pos: ref SZ.t) -> (#p: Ghost.erased SZ.t) ->
  stt bool
    (pts_to pos p ** vmatch x' x)
    (fun res -> exists* p' . pts_to pos p' ** vmatch x' x **
       pure (dry_post (enc x) (SZ.v p) res (SZ.v p')))

inline_for_extraction
fn sw_of (#t' #t: Type0) (#vmatch: t' -> t -> slprop) (#enc: t -> GTot SB.bytes)
  (w: W.r2l_writer_f vmatch enc) (d: dwf vmatch enc)
: swf #t' #t vmatch enc
= (x': t') (#x: Ghost.erased t) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  if (Dry? out) {
    let res = d x' #x pos;
    dry_finish out (enc x) #v #p res pos;
    res
  } else {
    let s = Wet?.s out;
    sbuf_wet_elim out s;
    let res = w x' #x s pos;
    sbuf_wet_intro out s;
    res
  }
}

(* Writing a sequence of bytes given by their indices *)
inline_for_extraction
fn sw_indexed
  (len: SZ.t)
  (f: (i: SZ.t { SZ.v i < SZ.v len }) -> U8.t)
  (e: Ghost.erased SB.bytes { Seq.length e == SZ.v len /\ (forall (i: nat) . i < SZ.v len ==> Seq.index e i == f (SZ.uint_to_t i)) })
  (out: sink)
  (pos: ref SZ.t)
  (#v: Ghost.erased SB.bytes)
  (#p: Ghost.erased SZ.t)
requires sbuf out v ** pts_to pos p ** pure (SZ.v p <= Seq.length v)
returns res: bool
ensures exists* v' p' . sbuf out v' ** pts_to pos p' ** pure (W.r2l_post e (SZ.v p) v res (SZ.v p') v')
{
  if (Dry? out) {
    let res = dry_sub len e pos;
    dry_finish out e #v #p res pos;
    res
  } else {
    let s = Wet?.s out;
    sbuf_wet_elim out s;
    let res = W.r2l_write_indexed len f e s pos;
    sbuf_wet_intro out s;
    res
  }
}

(* Identifiers *)
inline_for_extraction
fn sw_id
  (id: asn1_id_t)
  (out: sink)
  (pos: ref SZ.t)
  (#v: Ghost.erased SB.bytes)
  (#p: Ghost.erased SZ.t)
requires sbuf out v ** pts_to pos p ** pure (SZ.v p <= Seq.length v)
returns res: bool
ensures exists* v' p' . sbuf out v' ** pts_to pos p' ** pure (W.r2l_post (asn1_id_enc id) (SZ.v p) v res (SZ.v p') v')
{
  WL.asn1_id_enc_index_forall id;
  sw_indexed (WL.rt_id_len id) (WL.rt_id_byte id) (Ghost.hide (asn1_id_enc id)) out pos
}

(* Length headers *)
inline_for_extraction
fn dw_hdr (_: unit)
: dwf #SZ.t #nat W.vmatch_sz (enc_hdr true)
= (len: SZ.t) (#n: Ghost.erased nat) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
{
  unfold (W.vmatch_sz len n);
  fold (W.vmatch_sz len n);
  let n32 = SZ.sizet_to_uint32 len;
  assert_norm (pow2 32 == 4294967296);
  if (SZ.eq (SZ.uint32_to_sizet n32) len) {
    let y : LPB.bounded_int32 0 4294967295 = n32;
    WL.enc_len_eq_spec n32;
    let sz = DER.bounded_der_length32_size 0 4294967295 y;
    dry_sub sz (enc_hdr true n) pos
  } else {
    WL.enc_hdr_junk_forall true n;
    let vp = !pos;
    if (SZ.lt vp 3sz) {
      false
    } else if (SZ.lt (SZ.sub vp 3sz) len) {
      false
    } else {
      dry_sub (SZ.add len 3sz) (enc_hdr true n) pos
    }
  }
}

inline_for_extraction
let sw_hdr : swf #SZ.t #nat W.vmatch_sz (enc_hdr true) =
  sw_of (WL.r2l_write_hdr true) (dw_hdr ())

(* Constants *)

inline_for_extraction
let swc (e: SB.bytes) : Type = swf #unit #unit (prel_emp unit unit 1.0R) (WA.const_enc e)

let swcres (e: SB.bytes) (x': unit) (x: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (v: Ghost.erased SB.bytes) (p: Ghost.erased SZ.t)
: Type
= stt bool
    (sbuf out v ** pts_to pos p ** prel_emp unit unit 1.0R x' x ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . sbuf out v' ** pts_to pos p' ** prel_emp unit unit 1.0R x' x **
       pure (W.r2l_post (WA.const_enc e x) (SZ.v p) v res (SZ.v p') v'))

inline_for_extraction
fn sc_ext (#e1: Ghost.erased SB.bytes) (w: swc e1) (e2: Ghost.erased SB.bytes) (sq: squash (Ghost.reveal e1 == Ghost.reveal e2))
: swc e2
= (x': unit) (#x: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  w x' #x out pos
}

inline_for_extraction
fn sc_empty (_: unit)
: swc Seq.empty
= (x': unit) (#x: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  W.r2l_post_empty (SZ.v p) v;
  true
}

(* `w1` is written after (that is, to the left of) `w2` *)
inline_for_extraction
fn sc_append (#e1 #e2: Ghost.erased SB.bytes) (w1: swc e1) (w2: swc e2)
: swc (Seq.append e1 e2)
= (x': unit) (#x: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let res = w2 x' #x out pos;
  if (res) {
    with v1 p1 . assert (sbuf out v1 ** pts_to pos p1);
    let res' = w1 x' #x out pos;
    with v2 p2 . assert (sbuf out v2 ** pts_to pos p2);
    W.r2l_post_append e1 e2 (SZ.v p) v (SZ.v p1) v1 res' (SZ.v p2) v2;
    res'
  } else {
    W.r2l_post_false_weaken e2 (Seq.append e1 e2) (SZ.v p) v (SZ.v p) v;
    false
  }
}

inline_for_extraction
fn sc_byte (h: U8.t)
: swc (Seq.create 1 h)
= (x': unit) (#x: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  sw_indexed 1sz (fun _ -> h) (Ghost.hide (Seq.create 1 h)) out pos
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

(* A TLV, whose contents are written by `w` *)
inline_for_extraction
fn sw_tlv
  (id: asn1_id_t)
  (#t' #t: Type0)
  (#vmatch: t' -> t -> slprop)
  (#enc: t -> GTot SB.bytes)
  (w: swf vmatch enc)
: swf #t' #t vmatch (fun x -> enc_tlv id true (enc x))
= (x': t') (#x: Ghost.erased t) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let p0 = !pos;
  let ok = w x' #x out pos;
  if (ok) {
    with v1 p1 . assert (sbuf out v1 ** pts_to pos p1);
    let p1r = !pos;
    let len = SZ.sub p0 p1r;
    fold (W.vmatch_sz len (Seq.length (enc x)));
    let ok2 = sw_hdr len #(Seq.length (enc x)) out pos;
    unfold (W.vmatch_sz len (Seq.length (enc x)));
    with v2 p2 . assert (sbuf out v2 ** pts_to pos p2);
    frame_trans (SZ.v p) v (SZ.v p1) v1 v2;
    if ok2 {
      let ok3 = sw_id id out pos;
      with v3 p3 . assert (sbuf out v3 ** pts_to pos p3);
      frame_trans (SZ.v p) v (SZ.v p2) v2 v3;
      W.r2l_post_append (enc_hdr true (Seq.length (enc x))) (enc x) (SZ.v p) v (SZ.v p1) v1 true (SZ.v p2) v2;
      W.r2l_post_append (asn1_id_enc id) (enc_hdr true (Seq.length (enc x)) `Seq.append` enc x) (SZ.v p) v (SZ.v p2) v2 ok3 (SZ.v p3) v3;
      ok3
    } else {
      W.r2l_post_false_weaken (enc_hdr true (Seq.length (enc x)) `Seq.append` enc x) (enc_tlv id true (enc x)) (SZ.v p) v (SZ.v p) v2;
      false
    }
  } else {
    W.r2l_post_false_weaken (enc x) (enc_tlv id true (enc x)) (SZ.v p) v (SZ.v p) v;
    false
  }
}

[@@In.asn1_pulse_attr]
let rec sc_bytes ([@@@FStar.Attributes.monomorphize] l: list U8.t)
  (x': unit) (#x: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (swcres (Seq.seq_of_list l) x' x out pos v p)
  (decreases l)
= [@inline_let] let vf : swc (Seq.seq_of_list l) =
  (match l with
  | [] ->
    WA.seq_of_list_nil ();
    sc_ext (sc_empty ()) (Seq.seq_of_list l) ()
  | h :: t ->
    WA.seq_of_list_cons h t;
    sc_ext (sc_append (sc_byte h) (fun x' #x out pos #v #p -> sc_bytes t x' #x out pos #v #p)) (Seq.seq_of_list l) ())
  in vf x' #x out pos #v #p

inline_for_extraction
fn sc_arc (a: U32.t)
: swc (CE.enc_arc a)
= (x': unit) (#x: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  if (U32.lt a 128ul) {
    WA.enc_arc_short a;
    sw_indexed 1sz (fun _ -> Cast.uint32_to_uint8 a) (Ghost.hide (CE.enc_arc a)) out pos
  } else {
    WA.arc_index a;
    sw_indexed (WA.arc_len a) (WA.arc_byte a) (Ghost.hide (CE.enc_arc a)) out pos
  }
}

[@@In.asn1_pulse_attr]
let rec sc_arcs ([@@@FStar.Attributes.monomorphize] l: list U32.t)
  (x': unit) (#x: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (swcres (CE.list_enc CE.enc_arc l) x' x out pos v p)
  (decreases l)
= [@inline_let] let vf : swc (CE.list_enc CE.enc_arc l) =
  (match l with
  | [] -> sc_ext (sc_empty ()) (CE.list_enc CE.enc_arc l) ()
  | h :: t ->
    sc_ext (sc_append (sc_arc h) (fun x' #x out pos #v #p -> sc_arcs t x' #x out pos #v #p)) (CE.list_enc CE.enc_arc l) ())
  in vf x' #x out pos #v #p

inline_for_extraction
fn sc_tlv (id: asn1_id_t) (#e: Ghost.erased SB.bytes) (w: swc e)
: swc (enc_tlv id true e)
= (x': unit) (#x: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  sw_tlv id #unit #unit #(prel_emp unit unit 1.0R) #(WA.const_enc e) w x' #x out pos
}

[@@In.asn1_pulse_attr]
let rec sc_raw_key (kid: asn1_id_t) ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k)
  ([@@@FStar.Attributes.monomorphize] x: asn1_key_lit key_k)
  (x': unit) (#xx: Ghost.erased unit) (out: sink) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
: Tot (swcres (WA.raw_key_enc kid key_k x) x' xx out pos v p)
  (decreases key_k)
= [@inline_let] let vf : swc (WA.raw_key_enc kid key_k x) =
  (match key_k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    sc_ext (sc_tlv kid (fun x' #xx out pos #v #p -> sc_raw_key id2 k2 (In.prefixed_lit id2 k2 x) x' #xx out pos #v #p)) (WA.raw_key_enc kid key_k x) ()
  | ASN1_OID ->
    [@inline_let] let x' : asn1_oid_t = x in
    sc_ext (sc_tlv kid (fun x0 #xx out pos #v #p -> sc_arcs (In.oid_enc x') x0 #xx out pos #v #p)) (WA.raw_key_enc kid key_k x) ()
  | ASN1_RELATIVE_OID ->
    [@inline_let] let x' : asn1_relative_oid_t = x in
    sc_ext (sc_tlv kid (fun x0 #xx out pos #v #p -> sc_arcs x' x0 #xx out pos #v #p)) (WA.raw_key_enc kid key_k x) ()
  | _ ->
    sc_ext (sc_tlv kid (fun x0 #xx out pos #v #p -> sc_bytes (WA.raw_key_list key_k x) x0 #xx out pos #v #p)) (WA.raw_key_enc kid key_k x) ())
  in vf x' #xx out pos #v #p

(* The contents of a key literal (as `JK.cw_raw_key_c`) *)
[@@In.asn1_pulse_attr]
inline_for_extraction
let sc_raw_key_c ([@@@FStar.Attributes.monomorphize] key_k: asn1_terminal_k) ([@@@FStar.Attributes.monomorphize] x: asn1_key_lit key_k)
: swc (JK.raw_key_c key_k x)
= match key_k with
  | ASN1_PREFIXED_TERMINAL id2 k2 ->
    sc_ext (fun x' #xx out pos #v #p -> sc_raw_key id2 k2 (In.prefixed_lit id2 k2 x) x' #xx out pos #v #p) (JK.raw_key_c key_k x) ()
  | ASN1_OID ->
    [@inline_let] let x' : asn1_oid_t = x in
    sc_ext (fun x0 #xx out pos #v #p -> sc_arcs (In.oid_enc x') x0 #xx out pos #v #p) (JK.raw_key_c key_k x) ()
  | ASN1_RELATIVE_OID ->
    [@inline_let] let x' : asn1_relative_oid_t = x in
    sc_ext (fun x0 #xx out pos #v #p -> sc_arcs x' x0 #xx out pos #v #p) (JK.raw_key_c key_k x) ()
  | _ ->
    sc_ext (fun x0 #xx out pos #v #p -> sc_bytes (WA.raw_key_list key_k x) x0 #xx out pos #v #p) (JK.raw_key_c key_k x) ()

(* In-place operations *)

let insert_v (lt: SI.lt_t) (v: SB.bytes) (p2 p1 p0: nat) : GTot SB.bytes =
  if p2 <= p1 && p1 <= p0 && p0 <= Seq.length v
  then Seq.append (Seq.slice v 0 p2) (Seq.append (SI.ins lt (Seq.slice v p2 p1) (Seq.slice v p1 p0)) (Seq.slice v p0 (Seq.length v)))
  else v

let insert_v_post (lt: SI.lt_t) (v: SB.bytes) (p2 p1 p0: nat)
: Lemma (requires (p2 <= p1 /\ p1 <= p0 /\ p0 <= Seq.length v))
  (ensures (SI.insert_post lt v p2 p1 p0 (insert_v lt v p2 p1 p0)))
= SI.ins_length lt (Seq.slice v p2 p1) (Seq.slice v p1 p0);
  let v' = insert_v lt v p2 p1 p0 in
  assert (Seq.equal (Seq.slice v' p0 (Seq.length v)) (Seq.slice v p0 (Seq.length v)));
  assert (Seq.equal (Seq.slice v' p2 p0) (SI.ins lt (Seq.slice v p2 p1) (Seq.slice v p1 p0)))

inline_for_extraction
fn sk_insert (lt: SI.lt_t) (lt_impl: SI.lt_impl_t lt) (out: sink) (#v: Ghost.erased SB.bytes) (p2 p1 p0: SZ.t)
requires sbuf out v ** pure (SZ.v p2 <= SZ.v p1 /\ SZ.v p1 <= SZ.v p0 /\ SZ.v p0 <= Seq.length v)
ensures exists* v' . sbuf out v' ** pure (SI.insert_post lt v (SZ.v p2) (SZ.v p1) (SZ.v p0) v')
{
  if (Dry? out) {
    insert_v_post lt v (SZ.v p2) (SZ.v p1) (SZ.v p0);
    sbuf_dry_change out v (insert_v lt v (SZ.v p2) (SZ.v p1) (SZ.v p0))
  } else {
    let s = Wet?.s out;
    sbuf_wet_elim out s;
    SI.r2l_insert lt lt_impl s p2 p1 p0;
    sbuf_wet_intro out s
  }
}

let reverse_v (v: SB.bytes) (lo hi: nat) : GTot SB.bytes =
  if lo <= hi && hi <= Seq.length v
  then Seq.append (Seq.slice v 0 lo) (Seq.append (WI.seq_rev (Seq.slice v lo hi)) (Seq.slice v hi (Seq.length v)))
  else v

let reverse_v_post (v: SB.bytes) (lo hi: nat)
: Lemma (requires (lo <= hi /\ hi <= Seq.length v))
  (ensures (WI.reverse_range_post v lo hi (reverse_v v lo hi)))
= let v' = reverse_v v lo hi in
  assert (Seq.equal (Seq.slice v' 0 lo) (Seq.slice v 0 lo));
  assert (Seq.equal (Seq.slice v' hi (Seq.length v)) (Seq.slice v hi (Seq.length v)));
  assert (Seq.equal (Seq.slice v' lo hi) (WI.seq_rev (Seq.slice v lo hi)))

inline_for_extraction
fn sk_reverse_range (out: sink) (lo hi: SZ.t) (#v: Ghost.erased SB.bytes)
requires sbuf out v ** pure (SZ.v lo <= SZ.v hi /\ SZ.v hi <= Seq.length v)
ensures exists* v' . sbuf out v' ** pure (WI.reverse_range_post v (SZ.v lo) (SZ.v hi) v')
{
  if (Dry? out) {
    reverse_v_post v (SZ.v lo) (SZ.v hi);
    sbuf_dry_change out v (reverse_v v (SZ.v lo) (SZ.v hi))
  } else {
    let s = Wet?.s out;
    sbuf_wet_elim out s;
    WI.r2l_reverse_range s lo hi;
    sbuf_wet_intro out s
  }
}

(* Raw leaves (as `RW.raw_write_leaf`) *)

inline_for_extraction
let srw (#t: Type0) (r: bprel t) (pm: perm) = swf (r pm) id_enc

inline_for_extraction
let drw (#t: Type0) (r: bprel t) (pm: perm) = dwf (r pm) id_enc

inline_for_extraction
fn dw_boolean (pm: perm)
: drw #bool (raw_pure boolean_enc) pm
= (x': bool) (#x: Ghost.erased SB.bytes) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
{
  unfold (raw_pure boolean_enc pm x' x);
  fold (raw_pure boolean_enc pm x' x);
  dry_sub 1sz x pos
}

inline_for_extraction
fn dw_null (pm: perm)
: drw #unit (raw_pure null_enc) pm
= (x': unit) (#x: Ghost.erased SB.bytes) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
{
  unfold (raw_pure null_enc pm x' x);
  fold (raw_pure null_enc pm x' x);
  dry_sub 0sz x pos
}

inline_for_extraction
fn dw_i64_aux (i: I64.t) (x: Ghost.erased SB.bytes) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
requires pts_to pos p ** pure (Ghost.reveal x == i64_enc i)
returns res: bool
ensures exists* p' . pts_to pos p' ** pure (dry_post x (SZ.v p) res (SZ.v p'))
{
  WL.integer_enc_length 8 (i64_int i);
  dry_sub (WL.rt_int_len i) x pos
}

inline_for_extraction
fn dw_i64 (pm: perm)
: drw #I64.t raw_i64 pm
= (x': I64.t) (#x: Ghost.erased SB.bytes) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
{
  unfold (raw_i64 pm x' x);
  unfold (raw_pure i64_enc pm x' x);
  fold (raw_pure i64_enc pm x' x);
  fold (raw_i64 pm x' x);
  dw_i64_aux x' x pos
}

inline_for_extraction
fn dw_slice (pm: perm)
: drw #(S.slice U8.t) raw_slice pm
= (x': S.slice U8.t) (#x: Ghost.erased SB.bytes) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
{
  unfold (raw_slice pm x' x);
  unfold (prel_slice_ser id_enc pm x' x);
  S.pts_to_len x';
  fold (prel_slice_ser id_enc pm x' x);
  fold (raw_slice pm x' x);
  dry_sub (S.len x') x pos
}

inline_for_extraction
fn dw_int (pm: perm)
: drw #asn1_int_impl raw_int pm
= (x': asn1_int_impl) (#x: Ghost.erased SB.bytes) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
{
  match x' {
    Small i -> {
      rewrite (raw_int pm x' x) as (pure (Ghost.reveal x == i64_enc i));
      let res = dw_i64_aux i x pos;
      rewrite (pure (Ghost.reveal x == i64_enc i)) as (raw_int pm x' x);
      res
    }
    Big s -> {
      rewrite (raw_int pm x' x) as (raw_slice pm s x);
      let res = dw_slice pm s #x pos;
      rewrite (raw_slice pm s x) as (raw_int pm x' x);
      res
    }
  }
}

inline_for_extraction
fn dw_bitstring (pm: perm)
: drw #asn1_bitstring_impl raw_bitstring pm
= (x': asn1_bitstring_impl) (#x: Ghost.erased SB.bytes) (pos: ref SZ.t) (#p: Ghost.erased SZ.t)
{
  unfold (raw_bitstring pm x' x);
  with w . assert (S.pts_to x'.bytes #pm w);
  S.pts_to_len x'.bytes;
  fold (raw_bitstring pm x' x);
  let res = dry_sub (S.len x'.bytes) w pos;
  if (res) {
    dry_sub 1sz (W.enc_byte x'.unused) pos
  } else {
    false
  }
}

[@@In.asn1_pulse_attr]
inline_for_extraction
let dw_integer (bound: pos) (pm: perm) : drw (raw_integer bound) pm =
  if small_integer bound
  then coerce_eq () (dw_i64 pm)
  else coerce_eq () (dw_int pm)

[@@In.asn1_pulse_attr]
inline_for_extraction
let dw_leaf (k: leaf_k) (pm: perm) : drw (raw_leaf k) pm =
  match k with
  | ASN1_BOOLEAN -> dw_boolean pm
  | ASN1_NULL -> dw_null pm
  | ASN1_INTEGER bound -> dw_integer bound pm
  | ASN1_BITSTRING -> dw_bitstring pm
  | ASN1_OCTETSTRING -> dw_slice pm
  | ASN1_PRINTABLESTRING -> dw_slice pm
  | ASN1_UTF8STRING -> dw_slice pm
  | ASN1_IA5STRING -> dw_slice pm
  | ASN1_VISIBLESTRING -> dw_slice pm
  | ASN1_BMPSTRING -> dw_slice pm
  | ASN1_UNIVERSALSTRING -> dw_slice pm
  | ASN1_TELETEXSTRING -> dw_slice pm
  | ASN1_NUMERICSTRING -> dw_slice pm
  | ASN1_VIDEOTEXSTRING -> dw_slice pm
  | ASN1_GRAPHICSTRING -> dw_slice pm
  | ASN1_GENERALSTRING -> dw_slice pm
  | ASN1_OBJECTDESCRIPTOR -> dw_slice pm
  | ASN1_OID -> dw_slice pm
  | ASN1_RELATIVE_OID -> dw_slice pm
  | ASN1_OID_IRI -> dw_slice pm
  | ASN1_RELATIVE_OID_IRI -> dw_slice pm
  | ASN1_UTCTIME -> dw_slice pm
  | ASN1_GENERALIZEDTIME -> dw_slice pm
  | ASN1_DATE -> dw_slice pm
  | ASN1_TIME_OF_DAY -> dw_slice pm
  | ASN1_DATE_TIME -> dw_slice pm

[@@In.asn1_pulse_attr]
inline_for_extraction
let sw_leaf (k: leaf_k) (pm: perm) : srw (raw_leaf k) pm =
  sw_of (RW.raw_write_leaf k pm) (dw_leaf k pm)

inline_for_extraction
let sw_slice (pm: perm) : srw raw_slice pm =
  sw_of (RW.raw_write_slice pm) (dw_slice pm)
