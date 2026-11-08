module ASN1.Pulse.TypedWriter
#lang-pulse

(* A typed writer: it takes the same relation as the parsers,
   `ASN1.Pulse.Rel.arel false d pm x' v` with `v: asn1_t k`, plus `encodable k v`
   (which holds for every parsed value, `parsed_encodable_d`.) It converts
   the relation to the value-level relation of the raw writer
   (`ASN1.Pulse.RawVConv.arel_to_raw`), runs the raw writer
   (`ASN1.Pulse.RawJitWriter.jit_write_raw_d`), and converts back. Since
   `check_ser k () (forget k v) == Some v`, it never returns JIT_INVALID:
   - JIT_OK: `Ser.asn1_enc k v` was written right before the current position;
   - JIT_NO_SPACE: `Ser.asn1_enc k v` does not fit. *)

open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Raw
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
open ASN1.Pulse.JitWriter
open ASN1.Pulse.RawBytes
open ASN1.Pulse.RawJitWriter

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module SB = LowParse.Spec.Base
module W = LowParse.Pulse.R2L
module Ser = ASN1.Spec.Serializer
module Conf = ASN1.Spec.Conformance
module Can = ASN1.Spec.Raw.Canonical
module VC = ASN1.Pulse.RawVConv
module Trade = Pulse.Lib.Trade

let typed_jit_post (#s: _) (k: asn1_k s) (v: asn1_t k) (p: nat) (b: SB.bytes) (res: jit_result) (p': nat) (b': SB.bytes) : prop =
  Seq.length b' == Seq.length b /\
  p <= Seq.length b /\
  Seq.slice b' p (Seq.length b) == Seq.slice b p (Seq.length b) /\
  (res == JIT_OK ==> W.r2l_post (Ser.asn1_enc k v) p b true p' b') /\
  (res == JIT_NO_SPACE ==> Seq.length (Ser.asn1_enc k v) > p) /\
  (res == JIT_OK \/ res == JIT_NO_SPACE)

inline_for_extraction
let typed_jit_writer_d_t (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (pm: perm) =
  (x': t) -> (#v: Ghost.erased (asn1_t k)) ->
  (out: S.slice U8.t) -> (pos: ref SZ.t) -> (#b: Ghost.erased SB.bytes) -> (#p: Ghost.erased SZ.t) ->
  stt jit_result
    (pts_to out b ** pts_to pos p ** arel false d pm x' v ** pure (SZ.v p <= Seq.length b /\ Ser.encodable k v))
    (fun res -> exists* b' p' . pts_to out b' ** pts_to pos p' ** arel false d pm x' v **
      pure (typed_jit_post k v (SZ.v p) b res (SZ.v p') b'))

let typed_jit_correct (#s: _) (k: asn1_k s) (u: squash (raw_ok k)) (v: asn1_t k) (p: nat) (b: SB.bytes) (res: jit_result) (p': nat) (b': SB.bytes)
: Lemma
  (requires (Ser.encodable k v /\ raw_jit_post k u (forget k v) p b res p' b'))
  (ensures (typed_jit_post k v p b res p' b'))
= Can.check_ser_forget_encodable k () v

(* `wr` is meant to be `jit_write_raw_d d u pm (jit_writer_d d u (pm /. 2.0R))` *)
inline_for_extraction
fn write_typed_d (#s: _) (#k: asn1_k s) (#t: Type0) (d: adesc k t) (u: squash (raw_ok k)) (pm: perm)
  (wr: raw_jit_writer_d_t d u pm)
: typed_jit_writer_d_t d pm
= (x': t) (#v: Ghost.erased (asn1_t k))
  (out: S.slice U8.t) (pos: ref SZ.t) (#b: Ghost.erased SB.bytes) (#p: Ghost.erased SZ.t)
{
  VC.arel_to_raw d pm x' v;
  let res = wr x' #(forget k v) out pos;
  with b1 p1 . assert (pts_to out b1 ** pts_to pos p1);
  Trade.elim_trade _ _;
  typed_jit_correct k u v (SZ.v p) b res (SZ.v p1) b1;
  res
}

(* Every value returned by a parser is encodable, and its encoding is the
   parsed input, so parsing then writing round-trips. *)
let parsed_encodable_d (#s: _) (k: asn1_k s) (w: SB.bytes) (v: asn1_t k)
: Lemma
  (requires (Conf.wf k /\ parsed #asn1_strong_parser_kind (asn1_as_parser k) w v))
  (ensures (Ser.encodable k v /\ Ser.asn1_enc k v == w))
= Ser.parsed_encodable k w;
  Ser.asn1_as_parser_consumed k w;
  assert (Seq.equal (Seq.slice w 0 (Seq.length w)) w)
