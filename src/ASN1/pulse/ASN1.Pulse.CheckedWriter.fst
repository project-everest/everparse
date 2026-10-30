module ASN1.Pulse.CheckedWriter
#lang-pulse

(* Checked right-to-left writers.

   The writers of `ASN1.Pulse.Writer` require their input to be a typed
   value of the schema `k`, so their caller must establish all the
   constraints of the schema (value restrictions, DEFAULT components absent
   when equal to their default value, SET OF elements in DER order, etc.)
   A checked writer instead takes a typed value of the relaxed schema
   `relax k` (`ASN1.Spec.Relax`), which has the same Pulse representation
   type: it writes the value with the writer of `relax k`, then validates the
   bytes it wrote against `k`, and reports whether they are the DER encoding
   of a value of `k` (`CW_OK`), or not (`CW_INVALID`), or whether there is
   not enough room (`CW_NO_SPACE`). *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Value.Enc
open ASN1.Spec.ToValue
open ASN1.Spec.Relax
open ASN1.Pulse.Rel

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module SB = LowParse.Spec.Base
module LPB = LowParse.Pulse.Base
module Conf = ASN1.Spec.Conformance
module Ser = ASN1.Spec.Serializer
module RS = ASN1.Pulse.RelShare
module WLm = ASN1.Pulse.Writer.Lemmas
module Wr = ASN1.Pulse.Writer
module In = ASN1.Pulse.Interpreter
module W = LowParse.Pulse.R2L

type cw_result =
| CW_OK
| CW_NO_SPACE
| CW_INVALID

(* The static conditions on the schema, all decidable on a literal schema
   by normalization *)
let checked_ok (#s: _) (k: asn1_k s) : prop =
  In.supported_k k /\ Conf.wf k /\
  RS.wsupported_k (relax k) /\ Conf.wf (relax k) /\
  asn1_impl_t (relax k) == asn1_impl_t k

let relaxed_rel (#s: _) (k: asn1_k s) (u: squash (checked_ok k)) (pm: perm) (x: asn1_impl_t k) (y: asn1_t (relax k)) : slprop =
  asn1_rel (relax k) pm (coerce_eq () x) y

(* `enc` is the DER encoding of some value of `k` *)
let conforming (#s: _) (k: asn1_k s) (enc: SB.bytes) : prop =
  exists (x: asn1_t k) . Ser.encodable k x /\ Ser.asn1_enc k x == enc

let cw_post (#s: _) (k: asn1_k s) (enc: SB.bytes) (p: nat) (v: SB.bytes) (res: cw_result) (p': nat) (v': SB.bytes) : prop =
  Seq.length v' == Seq.length v /\
  p <= Seq.length v /\
  Seq.slice v' p (Seq.length v) == Seq.slice v p (Seq.length v) /\
  (res == CW_NO_SPACE <==> Seq.length enc > p) /\
  (res == CW_OK <==> (Seq.length enc <= p /\ conforming k enc)) /\
  (res == CW_OK ==> (p' + Seq.length enc == p /\ Seq.slice v' p' p == enc))

(* The encoding of a relaxed value conforms to `k` iff the relaxed value
   denotes the same generic DER value as some encodable value of `k`; by
   `ASN1.Spec.ToValue.Inj.to_value_inj`, the latter is unique. *)
let conforming_relax (#s: _) (k: asn1_k s) (y: asn1_t (relax k))
: Lemma (conforming k (WLm.kenc (relax k) y) <==>
    (exists (x: asn1_t k) . Ser.encodable k x /\ to_value k x == to_value (relax k) y))
= let prf (x: asn1_t k)
  : Lemma (Ser.asn1_enc k x == WLm.kenc (relax k) y <==> to_value k x == to_value (relax k) y)
  = Classical.move_requires (asn1_value_enc_inj (to_value k x)) (to_value (relax k) y)
  in
  Classical.forall_intro prf

(* Validating the written bytes decides conformance *)
let check_correct (#s: _) (k: asn1_k s) (enc: SB.bytes) (p: nat) (p1: SZ.t) (v1: SB.bytes) (valid: bool) (off: SZ.t)
: Lemma
  (requires (
    Conf.wf k /\
    SZ.v p1 + Seq.length enc == p /\ p <= Seq.length v1 /\
    Seq.slice v1 (SZ.v p1) p == enc /\
    LPB.validator_postcond #asn1_strong_parser_kind (asn1_as_parser k) p1 v1 off valid
  ))
  (ensures ((valid && SZ.v off = p) <==> conforming k enc))
= let b = Seq.slice v1 (SZ.v p1) (Seq.length v1) in
  Seq.slice_slice v1 (SZ.v p1) (Seq.length v1) 0 (Seq.length enc);
  assert (Seq.slice b 0 (Seq.length enc) `Seq.equal` enc);
  let fwd () : Lemma (requires (valid && SZ.v off = p)) (ensures (conforming k enc)) =
    Ser.parsed_spec_correct k b
  in
  let bwd (x: asn1_t k) : Lemma (requires (Ser.encodable k x /\ Ser.asn1_enc k x == enc)) (ensures (valid && SZ.v off = p)) =
    SB.parse_strong_prefix #asn1_strong_parser_kind (asn1_as_parser k) enc b
  in
  Classical.move_requires fwd ();
  Classical.forall_intro (Classical.move_requires bwd)

inline_for_extraction
let relaxed_writer (#s: _) (k: asn1_k s) (u: squash (checked_ok k)) (pm: perm)
: W.r2l_writer_f #(asn1_impl_t (relax k)) #(asn1_t (relax k)) (asn1_rel (relax k) pm) (WLm.kenc (relax k))
= fun x' #x out pos #v #p -> Wr.write_k (relax k) () pm x' #x out pos #v #p

inline_for_extraction
let validator (#s: _) (k: asn1_k s) (u: squash (checked_ok k))
: LPB.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k)
= fun input poffset #offset #pm #v -> In.validate_k k () input poffset #offset #pm #v

(* `w` and `vf` are meant to be `relaxed_writer k u pm` and `validator k u`,
   passed by the extraction root (with both unfolded by its
   normalize_for_extraction) so that `relax k` is normalized there, before
   Custard specializes `write_k` on it *)
inline_for_extraction
fn check_write_k (#s: _) (k: asn1_k s) (u: squash (checked_ok k)) (pm: perm)
  (w: W.r2l_writer_f #(asn1_impl_t (relax k)) #(asn1_t (relax k)) (asn1_rel (relax k) pm) (WLm.kenc (relax k)))
  (vf: LPB.validator #(asn1_t k) #asn1_strong_parser_kind (asn1_as_parser k))
  (x': asn1_impl_t k) (#y: Ghost.erased (asn1_t (relax k)))
  (out: S.slice U8.t) (pos: ref SZ.t) (#v: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
requires pts_to out v ** pts_to pos p ** relaxed_rel k u pm x' y ** pure (SZ.v p <= Seq.length v)
returns res: cw_result
ensures exists* v' p' . pts_to out v' ** pts_to pos p' ** relaxed_rel k u pm x' y **
  pure (cw_post k (WLm.kenc (relax k) y) (SZ.v p) v res (SZ.v p') v')
{
  let p0 = !pos;
  let x2 : asn1_impl_t (relax k) = coerce_eq () x';
  rewrite (relaxed_rel k u pm x' y) as (asn1_rel (relax k) pm x2 y);
  let ok = w x2 #y out pos;
  rewrite (asn1_rel (relax k) pm x2 y) as (relaxed_rel k u pm x' y);
  if (not ok) {
    CW_NO_SPACE
  } else {
    let p1 = !pos;
    with v1 . assert (pts_to out v1);
    let mut off = p1;
    let valid = vf out off;
    let off1 = !off;
    check_correct k (WLm.kenc (relax k) y) (SZ.v p0) p1 v1 valid off1;
    if (valid && off1 = p0) {
      CW_OK
    } else {
      CW_INVALID
    }
  }
}

(* The type of a checked writer for a schema `k` *)
inline_for_extraction
let checked_writer_t (#s: _) (k: asn1_k s) (u: squash (checked_ok k)) (pm: perm) =
  (x': asn1_impl_t k) -> (#y: Ghost.erased (asn1_t (relax k))) ->
  (out: S.slice U8.t) -> (pos: ref SZ.t) -> (#v: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt cw_result
    (pts_to out v ** pts_to pos p ** relaxed_rel k u pm x' y ** pure (SZ.v p <= Seq.length v))
    (fun res -> exists* v' p' . pts_to out v' ** pts_to pos p' ** relaxed_rel k u pm x' y **
      pure (cw_post k (WLm.kenc (relax k) y) (SZ.v p) v res (SZ.v p') v'))
