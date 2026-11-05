module ASN1.Pulse.RawJitWriter
#lang-pulse

(* A just-in-time right-to-left writer for raw values: given the Pulse
   representation `x'` of a raw value `y: asn1_raw_t k`
   (`asn1_raw_rel k pm x' y`), it writes the DER encoding of the typed
   value `check_ser k () y` if it exists and fits in the output buffer,
   and otherwise reports why it does not:
   - JIT_OK: `check_ser k () y == Some x`, and `Ser.asn1_enc k x` was
     written right before the current position;
   - JIT_INVALID: `check_ser k () y == None`;
   - JIT_NO_SPACE: if `check_ser k () y == Some x`, then `Ser.asn1_enc k x`
     does not fit.
   It never returns JIT_RETRY.

   It runs the JIT writer of raw bytes (`ASN1.Pulse.JitWriter.jit_writer`)
   on half of the permission, after splitting the raw value relation into
   the raw byte relation of its bytes `rb k y` (`ASN1.Pulse.RawBridge`.) *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Raw
open ASN1.Pulse.Rel
open ASN1.Pulse.RawRel
open ASN1.Pulse.RawValueRel
open ASN1.Pulse.JitWriter
open ASN1.Pulse.RawBytes

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module SB = LowParse.Spec.Base
module W = LowParse.Pulse.R2L
module Ser = ASN1.Spec.Serializer
module RW = ASN1.Pulse.RawWriter
module Br = ASN1.Pulse.RawBridge

let raw_jit_post (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (y: asn1_raw_t k) (p: nat) (v: SB.bytes) (res: jit_result) (p': nat) (v': SB.bytes) : prop =
  Seq.length v' == Seq.length v /\
  p <= Seq.length v /\
  Seq.slice v' p (Seq.length v) == Seq.slice v p (Seq.length v) /\
  (res == JIT_OK ==> (Some? (check_ser k () y) /\ W.r2l_post (Ser.asn1_enc k (Some?.v (check_ser k () y))) p v true p' v')) /\
  (res == JIT_NO_SPACE ==> (Some? (check_ser k () y) ==> Seq.length (Ser.asn1_enc k (Some?.v (check_ser k () y))) > p)) /\
  (res == JIT_INVALID ==> None? (check_ser k () y)) /\
  ~ (JIT_RETRY? res)

inline_for_extraction
let raw_jit_writer_t (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (pm: perm) =
  (x': asn1_impl_t k) -> (#y: Ghost.erased (asn1_raw_t k)) ->
  (out: S.slice U8.t) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt jit_result
    (pts_to out v ** pts_to pos p ** asn1_raw_rel k pm x' y ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** asn1_raw_rel k pm x' y **
      pure (raw_jit_post k u y (SZ.v p) v res (SZ.v p') v'))

let raw_jit_correct (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (y: asn1_raw_t k) (p: nat) (v: SB.bytes) (res: jit_result) (p': nat) (v': SB.bytes)
: Lemma
  (requires (jit_post_g true (rb k y) (kacc k (rb k y)) p v res p' v'))
  (ensures (raw_jit_post k u y p v res p' v'))
= match check_ser k () y with
  | Some _ -> rb_check_ser k u y
  | None -> if JIT_OK? res then rb_acc k u y else ()

let k_split (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) : Br.split_t (asn1_raw_rel k) (raw_rel k) (rb k) = (Br.br_k k u).sp
let k_absorb (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) : Br.absorb_t (asn1_raw_rel k) (raw_rel k) = (Br.br_k k u).ab

ghost
fn split_k (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (pm: perm) (x': asn1_impl_t k) (y: asn1_raw_t k)
requires asn1_raw_rel k pm x' y
ensures asn1_raw_rel k (pm /. 2.0R) x' y ** raw_rel k (pm /. 2.0R) x' (rb k y)
{
  k_split k u pm x' y
}

ghost
fn absorb_k (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (p1 p2: perm) (x': asn1_impl_t k) (y: asn1_raw_t k) (w: SB.bytes)
requires asn1_raw_rel k p1 x' y ** raw_rel k p2 x' w
ensures asn1_raw_rel k (p1 +. p2) x' y
{
  k_absorb k u p1 p2 x' y w
}

ghost
fn raw_rel_halves (#s: _) (k: asn1_k s) (pm: perm) (x': asn1_impl_t k) (y: asn1_raw_t k)
requires asn1_raw_rel k (pm /. 2.0R +. pm /. 2.0R) x' y
ensures asn1_raw_rel k pm x' y
{
  assert (pure (pm /. 2.0R +. pm /. 2.0R == pm));
  rewrite (asn1_raw_rel k (pm /. 2.0R +. pm /. 2.0R) x' y) as (asn1_raw_rel k pm x' y)
}

(* `wj` is meant to be `jit_writer k u (pm /. 2.0R)`, passed by the
   extraction root *)
inline_for_extraction
fn jit_write_raw (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (pm: perm)
  (wj: jwx (raw_rel k) (kacc k) (pm /. 2.0R))
: raw_jit_writer_t k u pm
= (x': asn1_impl_t k) (#y: Ghost.erased (asn1_raw_t k))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  split_k k u pm x' y;
  let res = wj x' #(rb k y) out pos;
  with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
  absorb_k k u (pm /. 2.0R) (pm /. 2.0R) x' y (rb k y);
  raw_rel_halves k pm x' y;
  raw_jit_correct k u y (SZ.v p) v res (SZ.v p1) v1;
  res
}

(* The same, for the Pulse type `t` of a descriptor `d` (with named
   structs and case types): a value `x': t` written as the raw bytes
   `rb k y` of a raw value `y` (`raw_arel d pm x' (rb k y)`), for which the
   writer reports the same outcomes as above. With the legacy descriptor,
   `asn1_raw_rel k pm x' y` implies this relation (`split_k`).
   `wj` is meant to be `jit_writer_d d u pm`. *)

inline_for_extraction
let raw_jit_writer_d_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (u: squash (raw_ok k)) (pm: perm) =
  (x': t) -> (#y: Ghost.erased (asn1_raw_t k)) ->
  (out: S.slice U8.t) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt jit_result
    (pts_to out v ** pts_to pos p ** raw_arel d pm x' (rb k y) ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** raw_arel d pm x' (rb k y) **
      pure (raw_jit_post k u y (SZ.v p) v res (SZ.v p') v'))

inline_for_extraction
fn jit_write_raw_d (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (u: squash (raw_ok k)) (pm: perm)
  (wj: jwx (raw_arel d) (kacc k) pm)
: raw_jit_writer_d_t d u pm
= (x': t) (#y: Ghost.erased (asn1_raw_t k))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  let res = wj x' #(rb k y) out pos;
  with v1 p1 . assert (pts_to out v1 ** pts_to pos p1);
  raw_jit_correct k u y (SZ.v p) v res (SZ.v p1) v1;
  res
}
