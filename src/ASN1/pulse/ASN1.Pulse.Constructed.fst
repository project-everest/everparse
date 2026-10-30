module ASN1.Pulse.Constructed
#lang-pulse
(* Generic validators for constructed types: SEQUENCE OF (and the list
   part of SET OF), CHOICE, and DEFAULT sequence items. *)
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.ILC
open ASN1.Spec.Choice
open ASN1.Spec.Sequence
open ASN1.Spec.Interpreter
open ASN1.Pulse.Sequence

module SZ = FStar.SizeT
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module SC = LowParse.Spec.Combinators
module SL = LowParse.Spec.List
module T = LowParse.Tot.Combinators
module SDER = LowParse.Spec.DER
module SVG = LowParse.Spec.VLGen
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC

(* Lists. Unlike LowParse.PulseParse.List.validate_list, the element parser
   may have a zero lower bound (ASN.1 TLVs have the weakest kind): the loop
   stops with a failure if an element consumes nothing, which is exactly the
   behavior of parse_list. *)

inline_for_extraction
fn validate_list_progress
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: SB.parser k t)
  (v: LPS.validator #t #k p)
: LPS.validator #(list t) #(SL.parse_list_kind k.parser_kind_injective) (SL.parse_list p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  S.pts_to_len input;
  let input_len = S.len input;
  let mut pcontinue = true;
  while (
    let c = !pcontinue;
    let off = !poffset;
    (c && SZ.lt off input_len)
  ) invariant exists* c off .
    R.pts_to pcontinue c **
    R.pts_to poffset off **
    S.pts_to input #pm v_bytes **
    pure (
      SZ.v off <= Seq.length v_bytes /\
      (c == true ==>
        (Some? (SB.parse (SL.parse_list p) (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes))) ==
         Some? (SB.parse (SL.parse_list p) (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes))))) /\
      (c == false ==> None? (SB.parse (SL.parse_list p) (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes))))
    )
    decreases %[(if !pcontinue then 1 else 0); (SZ.v input_len - SZ.v (!poffset))]
  {
    let off = !poffset;
    let s = Ghost.hide (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    SL.parse_list_eq p s;
    let is_valid = v input poffset;
    if is_valid {
      let off' = !poffset;
      if (off' = off) {
        pcontinue := false
      } else {
        Seq.slice_slice v_bytes (SZ.v off) (Seq.length v_bytes) (SZ.v off' - SZ.v off) (Seq.length v_bytes - SZ.v off);
      }
    } else {
      pcontinue := false
    }
  };
  let off = !poffset;
  let c = !pcontinue;
  if c {
    SL.parse_list_eq p (Seq.slice v_bytes (SZ.v off) (Seq.length v_bytes));
    SB.parser_kind_prop_equiv (SL.parse_list_kind k.parser_kind_injective) (SL.parse_list p);
    true
  } else {
    false
  }
}

let sized_list_eq (ne: bool) (#t: Type) (p: parser asn1_strong_parser_kind t) (b: bytes)
: Lemma (consumed #asn1_weak_parser_kind (parse_sized_list ne #asn1_strong_parser_kind #t p) b ==
    (if ne && Seq.length b = 0 then None else consumed (SL.parse_list #asn1_strong_parser_kind p) b))
= T.parse_filter_eq (LowParse.Tot.List.parse_list p) (list_size_ok ne) b;
  SL.parse_list_eq #asn1_strong_parser_kind p b

(* SEQUENCE OF: a list of TLVs filling the whole contents, non-empty if
   SIZE (1..MAX) *)
inline_for_extraction
fn validate_sized_list
  (ne: bool)
  (#t: Type0)
  (#p: parser asn1_strong_parser_kind t)
  (v: LPS.validator #t #asn1_strong_parser_kind p)
: LPS.validator #(sized_list ne t) #asn1_weak_parser_kind (parse_sized_list ne #asn1_strong_parser_kind #t p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v_bytes: Ghost.erased bytes)
{
  S.pts_to_len input;
  sized_list_eq ne p (Seq.slice v_bytes (SZ.v offset) (Seq.length v_bytes));
  let off = !poffset;
  if (ne && off = S.len input) {
    false
  } else {
    validate_list_progress #asn1_strong_parser_kind #t #p v input poffset
  }
}

(* An identifier followed by a payload depending on it *)

let id_then_prop
  (#k: parser_kind) (#t: Type) (p: SB.parser k t)
  (#kf: parser_kind) (#tf: Type) (fp: asn1_id_t -> SB.parser kf tf)
: prop
= forall (b: bytes) . consumed p b == (match SB.parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id, n) ->
      begin match consumed (fp id) (Seq.slice b n (Seq.length b)) with
      | None -> None
      | Some n' -> Some (n + n')
      end)

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_id_then
  (#t: Type0) (#k: Ghost.erased parser_kind) (p: SB.parser k t)
  (#tf: Type0) (#kf: Ghost.erased parser_kind) (fp: Ghost.erased (asn1_id_t -> SB.parser kf tf))
  (vfp: (id: asn1_id_t) -> LPS.validator #tf #kf (Ghost.reveal fp id))
  (sq: squash (id_then_prop p (Ghost.reveal fp)))
: LPS.validator #t #k p
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  assert (pure (consumed p sinput == (match SB.parse parse_asn1_identifier_U32 sinput with
    | None -> None
    | Some (id, n) ->
      begin match consumed (Ghost.reveal fp id) (Seq.slice sinput n (Seq.length sinput)) with
      | None -> None
      | Some n' -> Some (n + n')
      end)));
  let res = I.vread_identifier input poffset;
  match res {
    None -> { false }
    Some id -> {
      with off1 . assert (R.pts_to poffset off1);
      Seq.slice_slice v (SZ.v offset) (Seq.length v) (SZ.v off1 - SZ.v offset) (Seq.length v - SZ.v offset);
      vfp id input poffset
    }
  }
}

#pop-options

(* CHOICE *)

let synth_consumed (#k: parser_kind) (#t1 #t2: Type) (p: parser k t1) (f: t1 -> Tot t2 { synth_injective f }) (b: bytes)
: Lemma (consumed #k (T.parse_synth p f) b == consumed #k p b)
  [SMTPat (consumed #k (T.parse_synth p f) b)]
= T.parse_synth_eq p f b

let choice_id_then (lp: list (asn1_id_t & gen_parser asn1_strong_parser_kind))
: Lemma (id_then_prop
    (weaken asn1_strong_parser_kind (make_gen_choice_strong_parser parse_asn1_identifier_U32 lp))
    (parse_tagged_union_payload (project_tags lp) (make_gen_choice_strong_payload_parser lp)))
= let prf (b: bytes) : Lemma (consumed #asn1_strong_parser_kind (weaken asn1_strong_parser_kind (make_gen_choice_strong_parser parse_asn1_identifier_U32 lp)) b == (match SB.parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id, n) ->
      begin match consumed #asn1_strong_parser_kind (parse_tagged_union_payload (project_tags lp) (make_gen_choice_strong_payload_parser lp) id) (Seq.slice b n (Seq.length b)) with
      | None -> None
      | Some n' -> Some (n + n')
      end))
  = T.parse_tagged_union_eq parse_asn1_identifier_U32 (tag_of_gen_choice_type (extract_types lp)) (make_gen_choice_strong_payload_parser lp) b;
    match SB.parse parse_asn1_identifier_U32 b with
    | None -> ()
    | Some (id, n) ->
      SC.parse_synth_eq #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser lp id) (SC.synth_tagged_union_data (project_tags lp) id) (Seq.slice b n (Seq.length b))
  in
  Classical.forall_intro prf

let choice_payload_nil (id: asn1_id_t) (b: bytes)
: Lemma (None? (SB.parse (make_gen_choice_strong_payload_parser #asn1_id_t [] id) b))
= ()

let choice_payload_cons
  (hd: asn1_id_t & gen_parser asn1_strong_parser_kind)
  (tl: list (asn1_id_t & gen_parser asn1_strong_parser_kind))
  (id: asn1_id_t) (b: bytes)
: Lemma (consumed #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser (hd :: tl) id) b ==
    (if id = fst hd then consumed #asn1_strong_parser_kind (Mkgenparser?.p (snd hd)) b else consumed #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser tl id) b))
= if id = fst hd
  then T.parse_synth_eq (Mkgenparser?.p (snd hd)) (attach_tag (hd :: tl) id) b
  else T.parse_synth_eq (make_gen_choice_strong_payload_parser tl id) (fun x -> lemma_choice_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) id x) b

let asn1_choice_payload_cons
  (id': asn1_id_t) (ck: asn1_content_k)
  (tl: list (asn1_id_t & asn1_content_k))
  (id: asn1_id_t) (b: bytes)
: Lemma (consumed #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser (asn1_lc_as_parser ((id', ck) :: tl)) id) b ==
    (if id = id' then consumed #asn1_strong_parser_kind (parse_asn1_LC (asn1_content_as_parser ck)) b else consumed #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser (asn1_lc_as_parser tl) id) b))
= assert_norm (asn1_lc_as_parser ((id', ck) :: tl) == (id', Mkgenparser #asn1_strong_parser_kind (asn1_content_t ck) (parse_asn1_LC (asn1_content_as_parser ck))) :: asn1_lc_as_parser tl);
  choice_payload_cons (id', Mkgenparser #asn1_strong_parser_kind (asn1_content_t ck) (parse_asn1_LC (asn1_content_as_parser ck))) (asn1_lc_as_parser tl) id b

let asn1_choice_id_then (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc)))
: Lemma (id_then_prop #asn1_strong_parser_kind (asn1_as_parser (ASN1_CHOICE_ILC lc pf)) #asn1_strong_parser_kind (snd (asn1_as_parser_twin (ASN1_CHOICE_ILC lc pf))))
= choice_id_then (asn1_lc_as_parser lc)

let asn1_choice_twin_consumed (lc: list (asn1_id_t & asn1_content_k)) (pf: squash (List.Tot.noRepeats (List.Tot.map fst lc))) (id: asn1_id_t) (b: bytes)
: Lemma (consumed #asn1_strong_parser_kind (snd (asn1_as_parser_twin (ASN1_CHOICE_ILC lc pf)) id) b ==
    consumed #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser (asn1_lc_as_parser lc) id) b)
= let lp = asn1_lc_as_parser lc in
  SC.parse_synth_eq #asn1_strong_parser_kind (make_gen_choice_strong_payload_parser lp id) (SC.synth_tagged_union_data (project_tags lp) id) b

(* DEFAULT: the item is present iff it is not equal to the default value *)

let default_content (k: asn1_terminal_k) (defv: asn1_terminal_t k) : Tot asn1_content_k =
  ASN1_RESTRICTED_TERMINAL k (RESTRICT_CUSTOM (defaultv_filter defv))

#push-options "--z3rlimit 32"

let lc_filter_consumed (k: asn1_terminal_k) (f: asn1_terminal_t k -> bool) (b: bytes)
: Lemma (consumed #(parse_filter_kind asn1_strong_parser_kind) (T.parse_filter (parse_asn1_LC #(ASN1_TERMINAL k) (asn1_terminal_as_parser k)) f) b ==
    consumed #asn1_strong_parser_kind (parse_asn1_LC #(ASN1_RESTRICTED_TERMINAL k (RESTRICT_CUSTOM f)) (asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k (RESTRICT_CUSTOM f)))) b)
= let p = asn1_terminal_as_parser k in
  let pf = asn1_content_as_parser (ASN1_RESTRICTED_TERMINAL k (RESTRICT_CUSTOM f)) in
  let pl = SDER.parse_bounded_der_length32 0 ILC.asn1_length_max in
  T.parse_filter_eq (parse_asn1_LC #(ASN1_TERMINAL k) p) f b;
  ILC.lc_eq p b;
  ILC.lc_eq pf b;
  SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) pl #asn1_weak_parser_kind p b;
  SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) pl #asn1_weak_parser_kind pf b;
  match SB.parse pl b with
  | None -> ()
  | Some (len, sz) ->
    if Seq.length b < sz + U32.v len
    then ()
    else begin
      T.parse_filter_eq #asn1_weak_parser_kind p f (Seq.slice b sz (sz + U32.v len));
      T.parse_filter_eq #asn1_weak_parser_kind p (restriction_pred (RESTRICT_CUSTOM f)) (Seq.slice b sz (sz + U32.v len))
    end

let default_terminal_twin_consumed (id0: asn1_id_t) (#k: asn1_terminal_k) (defl: asn1_key_lit k) (id: asn1_id_t) (b: bytes)
: Lemma (consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin (ASN1_DEFAULT_TERMINAL id0 #k defl)) id) b ==
    (if id0 = id then consumed #asn1_strong_parser_kind (parse_asn1_LC (asn1_content_as_parser (default_content k (key_of_lit k defl)))) b else None))
= let defv = key_of_lit k defl in
  let fp = parse_asn1_ILC_twin id0 #(ASN1_TERMINAL k) (asn1_terminal_as_parser k) id in
  T.parse_filter_eq #asn1_strong_parser_kind fp (defaultv_filter defv) b;
  if id0 = id
  then lc_filter_consumed k (defaultv_filter defv) b
  else ()

let restricted_default_filter (#k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_terminal_t k) (x: asn1_terminal_t k) : Tot bool =
  restriction_pred r x && defaultv_filter defv x

let default_restricted_content (k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_terminal_t k) : Tot asn1_content_k =
  ASN1_RESTRICTED_TERMINAL k (RESTRICT_CUSTOM (restricted_default_filter r defv))

let lc_filter2_consumed (k: asn1_terminal_k) (r: asn1_restriction k) (defv: asn1_terminal_t k { restriction_pred r defv }) (b: bytes)
: Lemma (
    let p : asn1_weak_parser (parse_filter_refine (restriction_pred r)) = weaken _ (asn1_terminal_as_parser k `parse_filter` restriction_pred r) in
    consumed #(parse_filter_kind (parse_filter_kind asn1_strong_parser_kind))
      (T.parse_filter (T.parse_filter (parse_asn1_LC #(ASN1_RESTRICTED_TERMINAL k r) p) (restriction_pred r)) (defaultv_filter #(parse_filter_refine (restriction_pred r)) defv)) b ==
    consumed #asn1_strong_parser_kind (parse_asn1_LC (asn1_content_as_parser (default_restricted_content k r defv))) b)
= let p0 = asn1_terminal_as_parser k in
  let p : asn1_weak_parser (parse_filter_refine (restriction_pred r)) = weaken _ (p0 `parse_filter` restriction_pred r) in
  let pf = asn1_content_as_parser (default_restricted_content k r defv) in
  let pl = SDER.parse_bounded_der_length32 0 ILC.asn1_length_max in
  let q = T.parse_filter (parse_asn1_LC #(ASN1_RESTRICTED_TERMINAL k r) p) (restriction_pred r) in
  T.parse_filter_eq q (defaultv_filter #(parse_filter_refine (restriction_pred r)) defv) b;
  T.parse_filter_eq (parse_asn1_LC #(ASN1_RESTRICTED_TERMINAL k r) p) (restriction_pred r) b;
  ILC.lc_eq p b;
  ILC.lc_eq pf b;
  SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) pl #asn1_weak_parser_kind p b;
  SVG.parse_vlgen_weak_unfold 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) pl #asn1_weak_parser_kind pf b;
  match SB.parse pl b with
  | None -> ()
  | Some (len, sz) ->
    if Seq.length b < sz + U32.v len
    then ()
    else begin
      let b' = Seq.slice b sz (sz + U32.v len) in
      T.parse_filter_eq #asn1_weak_parser_kind p0 (restriction_pred r) b';
      T.parse_filter_eq #asn1_weak_parser_kind p0 (restriction_pred (RESTRICT_CUSTOM (restricted_default_filter r defv))) b'
    end

let default_restricted_twin_consumed (id0: asn1_id_t) (#k: asn1_terminal_k) (r: asn1_restriction k) (defl: asn1_key_lit k { restriction_pred r (key_of_lit k defl) }) (id: asn1_id_t) (b: bytes)
: Lemma (consumed #asn1_strong_parser_kind (parse_asn1_sequence_item_twin (asn1_decorated_as_parser_twin (ASN1_DEFAULT_RESTRICTED_TERMINAL id0 #k r defl)) id) b ==
    (if id0 = id then consumed #asn1_strong_parser_kind (parse_asn1_LC (asn1_content_as_parser (default_restricted_content k r (key_of_lit k defl)))) b else None))
= let defv : parse_filter_refine (restriction_pred r) = key_of_lit k defl in
  let p : asn1_weak_parser (parse_filter_refine (restriction_pred r)) = weaken _ (asn1_terminal_as_parser k `parse_filter` restriction_pred r) in
  let fp = parse_asn1_ILC_twin id0 #(ASN1_RESTRICTED_TERMINAL k r) p id in
  let q = T.parse_filter fp (restriction_pred r) in
  T.parse_filter_eq #asn1_strong_parser_kind fp (restriction_pred r) b;
  T.parse_filter_eq q (defaultv_filter #(parse_filter_refine (restriction_pred r)) defv) b;
  if id0 = id
  then lc_filter2_consumed k r defv b
  else ()

#pop-options

let default_null_fails (b: bytes)
: Lemma (None? (SB.parse (asn1_content_as_parser (default_content ASN1_NULL ())) b))
= T.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_NULL) (defaultv_filter #(asn1_terminal_t ASN1_NULL) ()) b
