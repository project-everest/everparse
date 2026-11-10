module ASN1.Pulse.AdbPrefixed
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Choice
open ASN1.Spec.Any
open ASN1.Spec.Interpreter
open ASN1.Pulse.Sequence
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module SCo = LowParse.Spec.Combinators
module SL = LowParse.Spec.List
module SFL = LowParse.Spec.FLData
module SVG = LowParse.Spec.VLGen
module SDER = LowParse.Spec.DER
module T = LowParse.Tot.Combinators
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC
module OID = ASN1.Pulse.OID
module ADB = ASN1.Pulse.AnyDefinedBy
open ASN1.Pulse.AnyDefinedBy

(* Tagged (EXPLICIT) keys: the key contents are an inner TLV, whose
   identifier is checked, and whose contents are compared recursively *)

let pt_val (id2: asn1_id_t) (k2: asn1_terminal_k) (x: asn1_terminal_t k2) : Tot (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2)) =
  assert_norm (asn1_terminal_t (ASN1_PREFIXED_TERMINAL id2 k2) == asn1_terminal_t k2);
  coerce_eq () x

let der_length_p = SDER.parse_bounded_der_length32 0 ILC.asn1_length_max

let prefixed_key_p (id2: asn1_id_t) (#k: parser_kind) (#t: Type) (p: SB.parser k t) =
  SCo.nondep_then
    (SCo.parse_filter #asn1_strong_parser_kind parse_asn1_identifier_U32 (fun id' -> id' = id2))
    (SVG.parse_vlgen_weak 0 ILC.asn1_length_max der_length_p p)

let prefixed_key_eq (id2: asn1_id_t) (#k: parser_kind) (#t: Type) (p: SB.parser k t) (b: bytes)
: Lemma (consumed (prefixed_key_p id2 p) b == (
    match SB.parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id', c1) ->
      if id' = id2
      then begin
        let b1 = Seq.slice b c1 (Seq.length b) in
        match SB.parse der_length_p b1 with
        | None -> None
        | Some (len, c2) ->
          match consumed (SFL.parse_fldata p (U32.v len)) (Seq.slice b1 c2 (Seq.length b1)) with
          | None -> None
          | Some c3 -> Some (c1 + c2 + c3)
      end
      else None
  ))
= SCo.nondep_then_eq (SCo.parse_filter #asn1_strong_parser_kind parse_asn1_identifier_U32 (fun id' -> id' = id2)) (SVG.parse_vlgen_weak 0 ILC.asn1_length_max der_length_p p) b;
  SCo.parse_filter_eq #asn1_strong_parser_kind parse_asn1_identifier_U32 (fun id' -> id' = id2) b;
  match SB.parse parse_asn1_identifier_U32 b with
  | Some (id', c1) ->
    let b1 = Seq.slice b c1 (Seq.length b) in
    SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max der_length_p p b1;
    begin match SB.parse der_length_p b1 with
    | Some (len, c2) ->
      let b2 = Seq.slice b1 c2 (Seq.length b1) in
      ADB.fldata_eq p (U32.v len) b2;
      if Seq.length b2 >= U32.v len
      then Seq.slice_slice b1 c2 (Seq.length b1) 0 (U32.v len)
    | None -> ()
    end
  | None -> ()

#push-options "--z3rlimit 128 --ifuel 2 --fuel 2"

#restart-solver

let prefixed_filter_consumed (id2: asn1_id_t) (k2: asn1_terminal_k) (x: asn1_terminal_t k2) (b: bytes)
: Lemma (consumed (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) (ADB.key_eq (pt_val id2 k2 x))) b ==
    consumed (prefixed_key_p id2 (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k2) (ADB.key_eq x))) b)
= let p2 = asn1_terminal_as_parser k2 in
  let f = SCo.parse_filter #asn1_weak_parser_kind p2 (ADB.key_eq x) in
  assert (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2) == weaken asn1_weak_parser_kind (ASN1.Spec.ILC.parse_asn1_ILC id2 #(ASN1_TERMINAL k2) p2));
  SCo.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) (ADB.key_eq (pt_val id2 k2 x)) b;
  ILC.ilc_eq id2 #(ASN1_TERMINAL k2) p2 b;
  prefixed_key_eq id2 f b;
  match SB.parse parse_asn1_identifier_U32 b with
  | Some (id', c1) ->
    if id' = id2
    then begin
      let b1 = Seq.slice b c1 (Seq.length b) in
      ILC.lc_eq p2 b1;
      ILC.length_eq b1;
      SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max der_length_p #asn1_weak_parser_kind #(asn1_terminal_t k2) p2 b1;
      match SB.parse der_length_p b1 with
      | Some (len, c2) ->
        let b2 = Seq.slice b1 c2 (Seq.length b1) in
        ADB.fldata_eq f (U32.v len) b2;
        if Seq.length b2 >= U32.v len
        then begin
          Seq.slice_slice b1 c2 (Seq.length b1) 0 (U32.v len);
          SCo.parse_filter_eq #asn1_weak_parser_kind p2 (ADB.key_eq x) (Seq.slice b2 0 (U32.v len))
        end
      | None -> ()
    end
  | None -> ()

#pop-options

let prefixed_key_fldata_consumed (id2: asn1_id_t) (k2: asn1_terminal_k) (x: asn1_terminal_t k2) (l: nat) (b: bytes)
: Lemma (consumed (ADB.key_eq_fldata (ASN1_PREFIXED_TERMINAL id2 k2) (pt_val id2 k2 x) l) b ==
    consumed (SFL.parse_fldata (prefixed_key_p id2 (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k2) (ADB.key_eq x))) l) b)
= ADB.fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_PREFIXED_TERMINAL id2 k2)) (ADB.key_eq (pt_val id2 k2 x))) l b;
  ADB.fldata_eq (prefixed_key_p id2 (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k2) (ADB.key_eq x))) l b;
  if Seq.length b >= l
  then prefixed_filter_consumed id2 k2 x (Seq.slice b 0 l)

#push-options "--z3rlimit 64"

inline_for_extraction
fn validate_prefixed_key (id2: asn1_id_t) (#k: Ghost.erased parser_kind) (#t: Type0) (#p: SB.parser k t)
  (vfl: (len: SZ.t) -> LPS.validator #t #(SFL.parse_fldata_kind (SZ.v len) k) (SFL.parse_fldata p (SZ.v len)))
: LPS.validator (prefixed_key_p id2 p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  prefixed_key_eq id2 p sinput;
  let r = I.vread_identifier input poffset;
  match r {
    None -> {
      false
    }
    Some id' -> {
      if (ILC.asn1_id_eq id' id2) {
        with off1 . assert (R.pts_to poffset off1);
        Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
        let rl = ILC.vread_length input poffset;
        match rl {
          None -> {
            false
          }
          Some len -> {
            let off2 = !poffset;
            Seq.slice_slice v (SZ.v off1) (Seq.length v) (SZ.v off2 - SZ.v off1) (Seq.length v - SZ.v off1);
            Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off2 - SZ.v offset) (Seq.length v - SZ.v offset);
            S.pts_to_len input;
            let remaining = SZ.sub (S.len input) off2;
            if LowParse.Pulse.SizeComparison.u32_lte_sizet len remaining {
              SZ.fits_lte (U32.v len) (SZ.v remaining);
              vfl (SZ.uint32_to_sizet len) input poffset
            } else {
              false
            }
          }
        }
      } else {
        false
      }
    }
  }
}

#pop-options
