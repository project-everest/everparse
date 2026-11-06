module ASN1.Pulse.OID
#lang-pulse
(* Validators for OBJECT IDENTIFIER and RELATIVE-OID contents (X.690 8.19,
   8.20): both are non-empty lists of base-128 subidentifiers covering the
   whole content. *)
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Content.OIDU32
open ASN1.Spec.Interpreter

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module Cast = FStar.Int.Cast
module LPS = LowParse.Pulse.Base
module T = LowParse.Tot.Combinators
module SC = LowParse.Spec.Combinators
module SL = LowParse.Spec.List
module I = ASN1.Pulse.Identifier

(* A subidentifier: parse_asn1_identifier_U32_alt *)

#push-options "--ifuel 2"
let head_alt_eq (buf: U8.t) (b: bytes)
: Lemma
  (requires (U8.v buf >= 128 /\ U8.v buf - 128 <> 0))
  (ensures (
    let state = initialize_partial_state (U8.sub buf 128uy) in
    match parse (parse_asn1_identifier_head_alt buf) b, parse (parse_asn1_identifier_head' state) b with
    | None, None -> True
    | Some (x, l), Some (x', l') -> (x <: U32.t) == (x' <: U32.t) /\ l == l'
    | _ -> False
  ))
= assert (parse_asn1_identifier_head_alt buf == parse_cast U32.t (fun x -> 0 < U32.v x /\ partial_state_prefixr (initialize_partial_state (U8.sub buf 128uy)) x) (fun _ -> True) (fun _ -> ()) (parse_asn1_identifier_head' (initialize_partial_state (U8.sub buf 128uy))));
  I.parse_cast_eq U32.t (fun x -> 0 < U32.v x /\ partial_state_prefixr (initialize_partial_state (U8.sub buf 128uy)) x) (fun _ -> True) (fun _ -> ()) (parse_asn1_identifier_head' (initialize_partial_state (U8.sub buf 128uy))) b
#pop-options

let head_alt_cast (state: asn1_partial_id_t) (x: asn1_partial_id_t {partial_state_prefixr state x}) : Tot U32.t = x

let head_alt_eq_all (buf: U8.t)
: Lemma
  (requires (U8.v buf >= 128 /\ U8.v buf - 128 <> 0))
  (ensures (
    let state = initialize_partial_state (U8.sub buf 128uy) in
    vread_map_prop #parse_asn1_identifier_head_kind (parse_asn1_identifier_head' state) (head_alt_cast state) #parse_asn1_identifier_head_kind (parse_asn1_identifier_head_alt buf)
  ))
= Classical.forall_intro (head_alt_eq buf)

inline_for_extraction
let vread_head_alt
  (buf : U8.t)
: vreader (parse_asn1_identifier_head_alt buf)
= ifthenelse_vreader (parse_asn1_identifier_head_alt buf)
    (U8.lt buf 128uy)
    (fun _ ->
      vread_ext #_ #parse_asn1_identifier_head_kind
        (vread_weaken parse_asn1_identifier_head_kind (vread_ret #U32.t (Cast.uint8_to_uint32 buf)) ())
        #parse_asn1_identifier_head_kind (parse_asn1_identifier_head_alt buf))
    (fun _ ->
      ifthenelse_vreader (parse_asn1_identifier_head_alt buf)
        (U8.sub buf 128uy = 0uy)
        (fun _ ->
          vread_ext #_ #parse_asn1_identifier_head_kind
            (vread_fail parse_asn1_identifier_head_kind U32.t)
            #parse_asn1_identifier_head_kind (parse_asn1_identifier_head_alt buf))
        (fun _ ->
          head_alt_eq_all buf;
          vread_let (parse_asn1_identifier_head_alt buf) (initialize_partial_state (U8.sub buf 128uy)) (fun state ->
          vread_map (I.vread_head' state) (head_alt_cast state)
            #parse_asn1_identifier_head_kind (parse_asn1_identifier_head_alt buf) ())))

let subid_kind = SC.and_then_kind LowParse.Spec.Int.parse_u8_kind parse_asn1_identifier_head_kind

let subid_eq (b: bytes)
: Lemma
  (requires (and_then_cases_injective parse_asn1_identifier_head_alt))
  (ensures (parse parse_asn1_identifier_U32_alt b ==
    parse (SC.and_then #_ #_ LowParse.Spec.Int.parse_u8 #parse_asn1_identifier_head_kind #_ (I.spec_of_tot_cont parse_asn1_identifier_head_alt)) b))
= I.tot_and_then_eq LowParse.Tot.Int.parse_u8 parse_asn1_identifier_head_alt b

let subid_spec : LowParse.Spec.Base.parser subid_kind U32.t =
  lemma_parse_asn1_identifier_head_alt_inj ();
  SC.and_then #_ #_ LowParse.Spec.Int.parse_u8 #parse_asn1_identifier_head_kind #_ (I.spec_of_tot_cont parse_asn1_identifier_head_alt)

let subid_spec_eq (b: bytes)
: Lemma (parse parse_asn1_identifier_U32_alt b == parse subid_spec b)
= lemma_parse_asn1_identifier_head_alt_inj ();
  subid_eq b

inline_for_extraction noextract
let vread_subid_spec
: vreader subid_spec
= lemma_parse_asn1_identifier_head_alt_inj ();
  vread_and_then #LowParse.Spec.Int.parse_u8_kind I.vread_u8 #parse_asn1_identifier_head_kind #_ #(I.spec_of_tot_cont parse_asn1_identifier_head_alt) vread_head_alt ()

(* A list of subidentifiers *)

let rec parse_list_ext
  (#k1: parser_kind) (#t: Type) (p1: LowParse.Spec.Base.parser k1 t)
  (#k2: parser_kind) (p2: LowParse.Spec.Base.parser k2 t)
  (b: bytes)
: Lemma
  (requires (forall x . parse p1 x == parse p2 x))
  (ensures (parse (SL.parse_list #k1 p1) b == parse (SL.parse_list #k2 p2) b))
  (decreases (Seq.length b))
= SL.parse_list_eq #k1 p1 b;
  SL.parse_list_eq #k2 p2 b;
  if Seq.length b = 0
  then ()
  else match parse p1 b with
  | None -> ()
  | Some (_, n) ->
    if n = 0 then () else parse_list_ext p1 p2 (Seq.slice b n (Seq.length b))

let subids = SL.parse_list subid_spec

(* Extracted once as a C function shared by OID and RELATIVE-OID *)
fn validate_subids_impl
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires S.pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: bool
  ensures S.pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (LPS.validator_postcond subids offset v off res))
{
  LowParse.PulseParse.List.validate_list (validate_of_vreader vread_subid_spec) () input poffset
}

(* OID and RELATIVE-OID: a non-empty list of subidentifiers *)

let nonempty_subids_prop (#k: parser_kind) (#t: Type) (p: LowParse.Spec.Base.parser k t) : prop =
  forall (b: bytes) . match parse p b, parse subids b with
  | None, None -> True
  | None, Some _ -> Seq.length b == 0
  | Some (_, n), Some (_, n') -> Seq.length b > 0 /\ n == n'
  | Some _, None -> False

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_nonempty_subids
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: LowParse.Spec.Base.parser k t)
  (sq: squash (nonempty_subids_prop p))
: LPS.validator #t #k p
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  S.pts_to_len input;
  let off = !poffset;
  if (off = S.len input) {
    false
  } else {
    validate_subids_impl input poffset
  }
}

#pop-options

let subids_eq (b: bytes)
: Lemma (parse (LowParse.Tot.List.parse_list parse_asn1_identifier_U32_alt) b == parse subids b)
= Classical.forall_intro subid_spec_eq;
  parse_list_ext #parse_asn1_identifier_first_kind parse_asn1_identifier_U32_alt subid_spec b

#push-options "--z3rlimit 64 --ifuel 2"

let oid_eq (b: bytes)
: Lemma (match parse (asn1_terminal_as_parser ASN1_OID) b, parse subids b with
  | None, None -> True
  | None, Some _ -> Seq.length b == 0
  | Some (_, n), Some (_, n') -> Seq.length b > 0 /\ n == n'
  | Some _, None -> False)
= lemma_synth_OIDU32_inj ();
  let p = parse_asn1_identifier_U32_alt `T.nondep_then` parse_asn1_OIDU32_tail in
  T.parse_synth_eq p synth_OIDU32 b;
  T.nondep_then_eq parse_asn1_identifier_U32_alt parse_asn1_OIDU32_tail b;
  subid_spec_eq b;
  subids_eq b;
  SL.parse_list_eq subid_spec b;
  LowParse.Spec.Base.parser_kind_prop_equiv subid_kind subid_spec;
  match parse subid_spec b with
  | Some (_, n) -> subids_eq (Seq.slice b n (Seq.length b))
  | _ -> ()

let relative_oid_eq (b: bytes)
: Lemma (match parse (asn1_terminal_as_parser ASN1_RELATIVE_OID) b, parse subids b with
  | None, None -> True
  | None, Some _ -> Seq.length b == 0
  | Some (_, n), Some (_, n') -> Seq.length b > 0 /\ n == n'
  | Some _, None -> False)
= T.parse_filter_eq parse_asn1_OIDU32_tail asn1_relative_oid_wf b;
  subids_eq b;
  SL.parse_list_eq subid_spec b;
  LowParse.Spec.Base.parser_kind_prop_equiv subid_kind subid_spec

#pop-options

inline_for_extraction
let validate_oid
: LPS.validator #(asn1_terminal_t ASN1_OID) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_OID)
= validate_nonempty_subids (asn1_terminal_as_parser ASN1_OID) (Classical.forall_intro oid_eq)

inline_for_extraction
let validate_relative_oid
: LPS.validator #(asn1_terminal_t ASN1_RELATIVE_OID) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_RELATIVE_OID)
= validate_nonempty_subids (asn1_terminal_as_parser ASN1_RELATIVE_OID) (Classical.forall_intro relative_oid_eq)
