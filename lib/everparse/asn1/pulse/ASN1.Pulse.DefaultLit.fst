module ASN1.Pulse.DefaultLit
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.ILC
open ASN1.Spec.Sequence
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
module SFL = LowParse.Spec.FLData
module SVG = LowParse.Spec.VLGen
module T = LowParse.Tot.Combinators
module ILC = ASN1.Pulse.ILC
module C = ASN1.Pulse.Constructed
module ADB = ASN1.Pulse.AnyDefinedBy
module AP = ASN1.Pulse.AdbPrefixed

(* DEFAULT values given as literals. DER forbids encoding a DEFAULT item
   whose value is the default, so the contents (of length l) of a present
   item are first matched against the literal, as with ANY DEFINED BY keys,
   and rejected if they match; otherwise they are validated as usual. *)

let lc_p (#k: parser_kind) (#t: Type) (p: SB.parser k t) =
  SVG.parse_vlgen_weak 0 ILC.asn1_length_max AP.der_length_p p

let lc_p_eq (#k: parser_kind) (#t: Type) (p: SB.parser k t) (b: bytes)
: Lemma (consumed (lc_p p) b == (
    match SB.parse AP.der_length_p b with
    | None -> None
    | Some (len, c2) ->
      match consumed (SFL.parse_fldata p (U32.v len)) (Seq.slice b c2 (Seq.length b)) with
      | None -> None
      | Some c3 -> Some (c2 + c3)
  ))
= SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(LowParse.Spec.DER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) AP.der_length_p #k p b;
  match SB.parse AP.der_length_p b with
  | Some (len, c2) ->
    let b2 = Seq.slice b c2 (Seq.length b) in
    ADB.fldata_eq p (U32.v len) b2;
    if Seq.length b2 >= U32.v len
    then Seq.slice_slice b c2 (Seq.length b) 0 (U32.v len)
  | None -> ()

#push-options "--z3rlimit 64"

let lc_custom_consumed (k: asn1_terminal_k) (f: asn1_terminal_t k -> bool) (b: bytes)
: Lemma (consumed #asn1_strong_parser_kind (parse_asn1_LC #(ASN1_RESTRICTED_TERMINAL k (RESTRICT_CUSTOM f)) (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k (RESTRICT_CUSTOM f)))) b ==
    consumed (lc_p (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) f)) b)
= let p0 = asn1_terminal_as_parser k in
  let pf = asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k (RESTRICT_CUSTOM f)) in
  let q = SCo.parse_filter #asn1_weak_parser_kind p0 f in
  ILC.lc_eq pf b;
  SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(LowParse.Spec.DER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) AP.der_length_p #asn1_weak_parser_kind pf b;
  SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(LowParse.Spec.DER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) AP.der_length_p #(SCo.parse_filter_kind asn1_weak_parser_kind) q b;
  match SB.parse AP.der_length_p b with
  | None -> ()
  | Some (len, sz) ->
    if Seq.length b < sz + U32.v len
    then ()
    else begin
      let b' = Seq.slice b sz (sz + U32.v len) in
      T.parse_filter_eq #asn1_weak_parser_kind p0 (restriction_pred (RESTRICT_CUSTOM f)) b';
      SCo.parse_filter_eq #asn1_weak_parser_kind p0 f b'
    end

let default_lc_consumed (k: asn1_terminal_k) (x: asn1_terminal_t k) (b: bytes)
: Lemma (consumed #asn1_strong_parser_kind (parse_asn1_LC (asn1_content_as_parser (C.default_content k x))) b ==
    consumed (lc_p (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (defaultv_filter x))) b)
= lc_custom_consumed k (defaultv_filter x) b

let default_restricted_lc_consumed (k: asn1_terminal_k) (r: asn1_restriction k) (x: asn1_terminal_t k) (b: bytes)
: Lemma (consumed #asn1_strong_parser_kind (parse_asn1_LC (asn1_content_as_parser (C.default_restricted_content k r x))) b ==
    consumed (lc_p (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (C.restricted_default_filter r x))) b)
= lc_custom_consumed k (C.restricted_default_filter r x) b

let neq_fl_consumed (k: asn1_terminal_k) (x: asn1_terminal_t k) (l: nat) (b: bytes)
: Lemma (consumed (SFL.parse_fldata (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (defaultv_filter x)) l) b ==
    (if Some? (consumed (ADB.key_eq_fldata k x l) b) then None else consumed (SFL.parse_fldata #asn1_weak_parser_kind (asn1_terminal_as_parser k) l) b))
= let p = asn1_terminal_as_parser k in
  ADB.fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind p (defaultv_filter x)) l b;
  ADB.fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind p (ADB.key_eq x)) l b;
  ADB.fldata_eq #asn1_weak_parser_kind p l b;
  if Seq.length b >= l
  then begin
    let b' = Seq.slice b 0 l in
    SCo.parse_filter_eq #asn1_weak_parser_kind p (defaultv_filter x) b';
    SCo.parse_filter_eq #asn1_weak_parser_kind p (ADB.key_eq x) b'
  end

let neq_fl_restricted_consumed (k: asn1_terminal_k) (r: asn1_restriction k) (x: asn1_terminal_t k) (l: nat) (b: bytes)
: Lemma (consumed (SFL.parse_fldata (SCo.parse_filter #asn1_weak_parser_kind (asn1_terminal_as_parser k) (C.restricted_default_filter r x)) l) b ==
    (if Some? (consumed (ADB.key_eq_fldata k x l) b) then None else consumed (SFL.parse_fldata #asn1_weak_parser_kind (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r)) l) b))
= let p = asn1_terminal_as_parser k in
  let pr : asn1_weak_parser (parse_filter_refine (restriction_pred r)) = weaken _ (p `T.parse_filter` restriction_pred r) in
  assert (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k r) == pr);
  ADB.fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind p (C.restricted_default_filter r x)) l b;
  ADB.fldata_eq #(SCo.parse_filter_kind asn1_weak_parser_kind) (SCo.parse_filter #asn1_weak_parser_kind p (ADB.key_eq x)) l b;
  ADB.fldata_eq #asn1_weak_parser_kind pr l b;
  if Seq.length b >= l
  then begin
    let b' = Seq.slice b 0 l in
    SCo.parse_filter_eq #asn1_weak_parser_kind p (C.restricted_default_filter r x) b';
    SCo.parse_filter_eq #asn1_weak_parser_kind p (ADB.key_eq x) b';
    T.parse_filter_eq #asn1_weak_parser_kind p (restriction_pred r) b'
  end

#pop-options

(* Reject if `ve` succeeds, otherwise validate with `va` from the same offset *)

inline_for_extraction
fn validate_neq
  (#te: Type0) (#ke: Ghost.erased parser_kind) (#pe: SB.parser ke te) (ve: LPS.validator pe)
  (#ta: Type0) (#ka: Ghost.erased parser_kind) (#pa: SB.parser ka ta) (va: LPS.validator pa)
  (#tn: Type0) (#kn: Ghost.erased parser_kind) (pn: SB.parser kn tn { forall b . consumed pn b == (if Some? (consumed pe b) then None else consumed pa b) })
: LPS.validator #tn #kn pn
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  assert (pure (consumed pn sinput == (if Some? (consumed pe sinput) then None else consumed pa sinput)));
  let off = !poffset;
  let is_eq = ve input poffset;
  if (is_eq) {
    false
  } else {
    poffset := off;
    va input poffset
  }
}

(* Contents preceded by their DER length, validated with a validator
   indexed by that length *)

#push-options "--z3rlimit 64"

inline_for_extraction
fn validate_lc_fl (#k: Ghost.erased parser_kind) (#t: Type0) (#p: SB.parser k t)
  (vfl: (len: SZ.t) -> LPS.validator #t #(SFL.parse_fldata_kind (SZ.v len) k) (SFL.parse_fldata p (SZ.v len)))
: LPS.validator (lc_p p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  lc_p_eq p sinput;
  let rl = ILC.vread_length input poffset;
  match rl {
    None -> {
      false
    }
    Some len -> {
      let off2 = !poffset;
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
}

#pop-options
