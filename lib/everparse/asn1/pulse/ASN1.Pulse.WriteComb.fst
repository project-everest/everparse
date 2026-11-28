module ASN1.Pulse.WriteComb
#lang-pulse

(* Combinators for the right-to-left raw writers (ASN1.Pulse.RawWriter):
   changing the relation and the encoder, ANY (already serialized), and a
   generic TLV jumper. *)

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

(* A generic jumper over TLV elements: the identifier and the length header
   give the size of the element *)

let jump_k_arith (r: option nat) (c off off2 l len: nat)
: Lemma (requires (r == Some c /\ off + Some?.v r == off2 + l /\ c <= len - off))
  (ensures (off + c == off2 + l /\ off2 + l <= len))
= ()

#push-options "--fuel 0 --ifuel 1"
let jump_k_post (#s: Ghost.erased (Set.set asn1_id_t)) (k: asn1_k s) (v: SB.bytes) (offset: SZ.t) (off1 off2: nat) (l: U32.t)
: Lemma
  (requires (SZ.fits (Seq.length v) /\
    SZ.v offset <= Seq.length v /\
    Some? (SB.parse (asn1_as_parser k <: SB.parser asn1_strong_parser_kind (asn1_t k)) (Seq.slice v (SZ.v offset) (Seq.length v))) /\
    (match SB.parse parse_asn1_identifier_U32 (Seq.slice v (SZ.v offset) (Seq.length v)) with Some (_, c) -> off1 == SZ.v offset + c | None -> False) /\
    off1 <= Seq.length v /\
    (match SB.parse (LowParse.Spec.DER.parse_bounded_der_length32 0 ILC.asn1_length_max) (Seq.slice v off1 (Seq.length v)) with Some (len', c2) -> (len' <: U32.t) == l /\ off2 == off1 + c2 | None -> False)))
  (ensures (SZ.fits (off2 + U32.v l) /\
    (match SB.parse (asn1_as_parser k <: SB.parser asn1_strong_parser_kind (asn1_t k)) (Seq.slice v (SZ.v offset) (Seq.length v)) with
     | Some (_, c) -> SZ.v offset + c == off2 + U32.v l
     | None -> False)))
= let b = Seq.slice v (SZ.v offset) (Seq.length v) in
  PSO.tlv_size_at v (SZ.v offset) off1 off2 l;
  PSO.tlv_consumed k b;
  match SB.parse (asn1_as_parser k <: SB.parser asn1_strong_parser_kind (asn1_t k)) b with
  | Some (_, c) ->
    jump_k_arith (ASN1.Pulse.ParseSequence.Lemmas.tlv_size b) c (SZ.v offset) off2 (U32.v l) (Seq.length v);
    SZ.fits_lte (off2 + U32.v l) (Seq.length v)
#pop-options

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
          jump_k_post k v offset (SZ.v off1) (SZ.v off2) l;
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
