module ASN1.Pulse.Any
#lang-pulse
(* Validators for ANY: generic DER values (ASN1.Spec.Value), using the
   constant-stack validator of LowParse.Pulse.RecursiveVLGen. The
   validator is extracted as a single C function, called once per ANY
   (stack usage does not depend on the nesting depth of the value.) *)
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.LengthU32
open ASN1.Spec.Value
open ASN1.Spec.Interpreter
open ASN1.Pulse.Sequence

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module SB = LowParse.Spec.Base
module T = LowParse.Tot.Combinators
module RV = LowParse.Pulse.RecursiveVLGen
module SVG = LowParse.Spec.VLGen
module SDER = LowParse.Spec.DER
module PPVG = LowParse.PulseParse.VLGen
module PPFL = LowParse.PulseParse.FLData
module PPL = LowParse.PulseParse.List
module SFL = LowParse.Spec.FLData
module SCmp = LowParse.Pulse.SizeComparison
module I = ASN1.Pulse.Identifier
module ILC = ASN1.Pulse.ILC
module Term = ASN1.Pulse.Terminal

(* Identifiers *)

inline_for_extraction
let always_constructed_impl (v: U32.t) : Tot (b: bool { b == asn1_universal_always_constructed v }) =
  v = 8ul || v = 11ul || v = 16ul || v = 17ul || v = 29ul

inline_for_extraction
let any_id_valid_impl (id: asn1_id_t) : Tot (b: bool { b == asn1_any_id_valid id }) =
  match id with
  | MK_ASN1_ID UNIVERSAL f v ->
    v <> 0ul && v <> 15ul &&
    begin match f with
    | CONSTRUCTED -> always_constructed_impl v || U32.gt v 36ul
    | PRIMITIVE -> not (always_constructed_impl v)
    end
  | _ -> true

let any_identifier_eq (b: bytes)
: Lemma
  (parse parse_asn1_any_identifier b == (
    match parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id, c) -> if asn1_any_id_valid id then Some (id, c) else None
  ))
= lemma_parse_asn1_identifier_first_inj ();
  T.parse_filter_eq (LowParse.Tot.Int.parse_u8 `T.and_then` parse_asn1_identifier_first) asn1_any_id_valid b

fn vread_any_identifier
  (input: S.slice byte)
  (poffset: ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires S.pts_to input #pm v ** pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: option asn1_any_id_t
  ensures S.pts_to input #pm v ** (exists* off . pts_to poffset off ** pure (vreader_postcond #asn1_any_identifier_kind #asn1_any_id_t parse_asn1_any_identifier offset v off res))
{
  any_identifier_eq (Seq.slice v (SZ.v offset) (Seq.length v));
  let r = I.vread_identifier input poffset;
  match r {
    None -> { None #asn1_any_id_t }
    Some id -> {
      if (any_id_valid_impl id) {
        Some #asn1_any_id_t id
      } else {
        None #asn1_any_id_t
      }
    }
  }
}

(* Lengths *)

inline_for_extraction
let vread_any_length : vreader #(LowParse.Spec.BoundedInt.bounded_int32 0 4294967295) #parse_asn1_length_u32_t_kind parse_asn1_length_u32_t =
  Classical.forall_intro ILC.length_eq;
  vread_ext ILC.vread_length #parse_asn1_length_u32_t_kind parse_asn1_length_u32_t

(* Headers *)

#push-options "--z3rlimit 64"

#restart-solver

fn read_header_any_impl
  (input: S.slice byte)
  (pos: SZ.t)
  (bound: SZ.t)
  (pcs: R.ref SZ.t)
  (pce: R.ref SZ.t)
  (pisn: R.ref bool)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (#cs0: Ghost.erased SZ.t)
  (#ce0: Ghost.erased SZ.t)
  (#isn0: Ghost.erased bool)
  requires pts_to input #pm v ** R.pts_to pcs cs0 ** R.pts_to pce ce0 ** R.pts_to pisn isn0 ** pure (SZ.v pos <= SZ.v bound /\ SZ.v bound <= Seq.length v)
  returns res: bool
  ensures pts_to input #pm v ** (exists* cs ce isn . R.pts_to pcs cs ** R.pts_to pce ce ** R.pts_to pisn isn ** pure (RV.read_header_post asn1_value_param v pos bound cs ce isn res))
{
  RV.rec_vlgen_hdr_eq asn1_value_param v (SZ.v pos);
  let mut poff = pos;
  let oid = vread_any_identifier input poff;
  match oid {
    None -> { false }
    Some id -> {
      let tag_end = !poff;
      let olen = vread_any_length input poff;
      match olen {
        None -> { false }
        Some len -> {
          let len_end = !poff;
          if (SZ.gt len_end bound) {
            false
          } else {
            let rem = SZ.sub bound len_end;
            if (LowParse.Pulse.SizeComparison.u32_lte_sizet len rem) {
              SZ.fits_lte (U32.v len) (SZ.v rem);
              let l = SZ.uint32_to_sizet len;
              pcs := len_end;
              pce := SZ.add len_end l;
              pisn := CONSTRUCTED? (MK_ASN1_ID?.f id);
              true
            } else {
              false
            }
          }
        }
      }
    }
  }
}

#pop-options

inline_for_extraction
let read_header_any : RV.read_header_t asn1_value_param = read_header_any_impl

(* Leaves: if the identifier is a known universal type, the contents must
   be a valid encoding of that type *)

let any_leaf_consumed (id: asn1_any_id_t) (b: bytes)
: Lemma (consumed #asn1_weak_parser_kind (parse_asn1_any_leaf id) b == (if asn1_any_leaf_ok id b then Some (Seq.length b) else None))
= T.parse_synth_eq (LowParse.Tot.SeqBytes.parse_seq_all_bytes `T.parse_filter` asn1_any_leaf_ok id) (synth_asn1_any_leaf id) b;
  T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes (asn1_any_leaf_ok id) b

let leaf_matches (id: asn1_any_id_t) (#k: parser_kind) (#t: Type) (p: SB.parser k t) : prop =
  forall (b: bytes) . asn1_any_leaf_ok id b == (match SB.parse p b with Some (_, c) -> c = Seq.length b | None -> false)

let universal_parser_eq (k: asn1_terminal_k { not (ASN1_PREFIXED_TERMINAL? k) }) (b: bytes)
: Lemma (parse (asn1_universal_terminal_parser k) b == parse (asn1_terminal_as_parser k) b)
= match k with
  | ASN1_BOOLEAN -> ()
  | ASN1_INTEGER _ -> ()
  | ASN1_BITSTRING -> ()
  | ASN1_OCTETSTRING -> ()
  | ASN1_UTF8STRING -> ()
  | ASN1_PRINTABLESTRING -> ()
  | ASN1_IA5STRING -> ()
  | ASN1_VISIBLESTRING -> ()
  | ASN1_BMPSTRING -> ()
  | ASN1_UNIVERSALSTRING -> ()
  | ASN1_TELETEXSTRING -> ()
  | ASN1_NUMERICSTRING -> ()
  | ASN1_VIDEOTEXSTRING -> ()
  | ASN1_GRAPHICSTRING -> ()
  | ASN1_GENERALSTRING -> ()
  | ASN1_OBJECTDESCRIPTOR -> ()
  | ASN1_NULL -> ()
  | ASN1_OID -> ()
  | ASN1_RELATIVE_OID -> ()
  | ASN1_OID_IRI -> ()
  | ASN1_RELATIVE_OID_IRI -> ()
  | ASN1_UTCTIME -> ()
  | ASN1_GENERALIZEDTIME -> ()
  | ASN1_DATE -> ()
  | ASN1_TIME_OF_DAY -> ()
  | ASN1_DATE_TIME -> ()

let leaf_case (id: asn1_any_id_t) (k: asn1_terminal_k)
: Lemma
  (requires (UNIVERSAL? (MK_ASN1_ID?.c id) /\ asn1_universal_terminal (MK_ASN1_ID?.v id) == Some k /\ not (ASN1_PREFIXED_TERMINAL? k)))
  (ensures (leaf_matches id #asn1_weak_parser_kind (asn1_terminal_as_parser k)))
= Classical.forall_intro (universal_parser_eq k)

let octetstring_all (b: bytes)
: Lemma (match parse (asn1_terminal_as_parser ASN1_OCTETSTRING) b with Some (_, c) -> c == Seq.length b | None -> False)
= ()

let leaf_all (id: asn1_any_id_t)
: Lemma
  (requires (
    UNIVERSAL? (MK_ASN1_ID?.c id) ==> (
      match asn1_universal_terminal (MK_ASN1_ID?.v id) with
      | None -> True
      | Some k -> k == ASN1_OCTETSTRING \/ k == ASN1_TELETEXSTRING \/ k == ASN1_VIDEOTEXSTRING \/
        k == ASN1_GRAPHICSTRING \/ k == ASN1_GENERALSTRING \/ k == ASN1_OBJECTDESCRIPTOR
  )))
  (ensures (forall (b: bytes) . asn1_any_leaf_ok id b == true))
= Classical.forall_intro octetstring_all

#push-options "--z3rlimit 32"

inline_for_extraction
fn check_leaf
  (id: asn1_any_id_t)
  (#t: Type0) (#k: Ghost.erased parser_kind) (#p: SB.parser k t)
  (w: LPS.validator p)
  (sq: squash (leaf_matches id p))
: LPS.validator #asn1_octetstring_t #asn1_weak_parser_kind (parse_asn1_any_leaf id)
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  any_leaf_consumed id (Seq.slice v (SZ.v offset) (Seq.length v));
  pts_to_len input;
  let ok = w input poffset;
  if ok {
    let off = !poffset;
    (off = S.len input)
  } else {
    false
  }
}

inline_for_extraction
fn accept_leaf
  (id: asn1_any_id_t)
  (sq: squash (forall (b: bytes) . asn1_any_leaf_ok id b == true))
: LPS.validator #asn1_octetstring_t #asn1_weak_parser_kind (parse_asn1_any_leaf id)
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  any_leaf_consumed id (Seq.slice v (SZ.v offset) (Seq.length v));
  pts_to_len input;
  poffset := S.len input;
  true
}

(* INTEGER with the ANY bound (2^32 - 1 bytes): the bound is checked
   without assuming that size_t has more than 32 bits *)
inline_for_extraction
fn validate_integer_any (_: unit)
: LPS.validator #(asn1_terminal_t (ASN1_INTEGER asn1_any_integer_bound)) #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_INTEGER asn1_any_integer_bound))
=
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let off = !poffset;
  pts_to_len input;
  let len = S.len input;
  let n = SZ.sub len off;
  let big = SCmp.u64_lte_sizet 4294967296UL n;
  if (big || n = 0sz) {
    false
  } else if (n = 1sz) {
    poffset := len;
    true
  } else {
    let c0 = input.(off);
    let c1 = input.(SZ.add off 1sz);
    if ((c0 = 0uy && U8.lt c1 128uy) || (c0 = 255uy && U8.lt 127uy c1)) {
      false
    } else {
      poffset := len;
      true
    }
  }
}

#pop-options

#push-options "--z3rlimit 128 --fuel 1 --ifuel 1"

#restart-solver

fn validate_any_leaf_impl
  (id: asn1_any_id_t)
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: bool
  ensures pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (LPS.validator_postcond #asn1_weak_parser_kind (parse_asn1_any_leaf id) offset v off res))
{
  if (UNIVERSAL? (MK_ASN1_ID?.c id)) {
    let t = MK_ASN1_ID?.v id;
    if (t = 4ul || t = 7ul || t = 20ul || t = 21ul || t = 25ul || t = 27ul) {
      leaf_all id;
      accept_leaf id () input poffset
    } else if (t = 1ul) {
      leaf_case id ASN1_BOOLEAN;
      check_leaf id Term.validate_boolean () input poffset
    } else if (t = 2ul || t = 10ul) {
      leaf_case id (ASN1_INTEGER asn1_any_integer_bound);
      check_leaf id (validate_integer_any ()) () input poffset
    } else if (t = 3ul) {
      leaf_case id ASN1_BITSTRING;
      check_leaf id Term.validate_bitstring () input poffset
    } else if (t = 5ul) {
      leaf_case id ASN1_NULL;
      check_leaf id Term.validate_null () input poffset
    } else if (t = 6ul) {
      leaf_case id ASN1_OID;
      check_leaf id ASN1.Pulse.OID.validate_oid () input poffset
    } else if (t = 12ul) {
      leaf_case id ASN1_UTF8STRING;
      check_leaf id Term.validate_utf8 () input poffset
    } else if (t = 13ul) {
      leaf_case id ASN1_RELATIVE_OID;
      check_leaf id ASN1.Pulse.OID.validate_relative_oid () input poffset
    } else if (t = 18ul) {
      leaf_case id ASN1_NUMERICSTRING;
      check_leaf id Term.validate_numeric () input poffset
    } else if (t = 19ul) {
      leaf_case id ASN1_PRINTABLESTRING;
      check_leaf id Term.validate_printable () input poffset
    } else if (t = 22ul) {
      leaf_case id ASN1_IA5STRING;
      check_leaf id Term.validate_ia5 () input poffset
    } else if (t = 23ul) {
      leaf_case id ASN1_UTCTIME;
      check_leaf id Term.validate_utctime () input poffset
    } else if (t = 24ul) {
      leaf_case id ASN1_GENERALIZEDTIME;
      check_leaf id Term.validate_generalizedtime () input poffset
    } else if (t = 26ul) {
      leaf_case id ASN1_VISIBLESTRING;
      check_leaf id Term.validate_visible () input poffset
    } else if (t = 28ul) {
      leaf_case id ASN1_UNIVERSALSTRING;
      check_leaf id Term.validate_universal () input poffset
    } else if (t = 30ul) {
      leaf_case id ASN1_BMPSTRING;
      check_leaf id Term.validate_bmp () input poffset
    } else if (t = 31ul) {
      leaf_case id ASN1_DATE;
      check_leaf id Term.validate_date () input poffset
    } else if (t = 32ul) {
      leaf_case id ASN1_TIME_OF_DAY;
      check_leaf id Term.validate_timeofday () input poffset
    } else if (t = 33ul) {
      leaf_case id ASN1_DATE_TIME;
      check_leaf id Term.validate_datetime () input poffset
    } else if (t = 35ul) {
      leaf_case id ASN1_OID_IRI;
      check_leaf id Term.validate_oid_iri () input poffset
    } else if (t = 36ul) {
      leaf_case id ASN1_RELATIVE_OID_IRI;
      check_leaf id Term.validate_relative_oid_iri () input poffset
    } else {
      leaf_all id;
      accept_leaf id () input poffset
    }
  } else {
    leaf_all id;
    accept_leaf id () input poffset
  }
}

#pop-options

inline_for_extraction
let validate_any_leaf (id: asn1_any_id_t) : LPS.validator #asn1_octetstring_t #asn1_weak_parser_kind (parse_asn1_any_leaf id) =
  validate_any_leaf_impl id

(* The leaf validator of the recursive validator: re-reads the identifier,
   then validates the contents [cs, ce) *)

let fldata_eq (#k: parser_kind) (#t: Type) (p: SB.parser k t) (sz: nat) (b: bytes)
: Lemma (SB.parse (SFL.parse_fldata p sz) b == (
    if Seq.length b < sz
    then None
    else match SB.parse p (Seq.slice b 0 sz) with
    | Some (x, c) -> if c = sz then Some (x, sz) else None
    | None -> None
  ))
= ()

#push-options "--z3rlimit 64"

#restart-solver

fn validate_any_fl_impl
  (input: S.slice byte)
  (pos: SZ.t)
  (cs: SZ.t)
  (ce: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** pure (RV.validate_leaf_pre asn1_value_param v pos cs ce)
  returns res: bool
  ensures pts_to input #pm v ** pure (RV.validate_leaf_post asn1_value_param v pos cs ce res)
{
  RV.rec_vlgen_hdr_eq asn1_value_param v (SZ.v pos);
  let mut poff = pos;
  let oid = vread_any_identifier input poff;
  match oid {
    None -> { false }
    Some id -> {
      poff := cs;
      fldata_eq #asn1_weak_parser_kind (parse_asn1_any_leaf id) (SZ.v ce - SZ.v cs) (Seq.slice v (SZ.v cs) (Seq.length v));
      Seq.slice_slice v (SZ.v cs) (Seq.length v) 0 (SZ.v ce - SZ.v cs);
      PPFL.validate_fldata (validate_any_leaf id) (SZ.sub ce cs) input poff
    }
  }
}

#pop-options

inline_for_extraction
let validate_any_fl : RV.validate_leaf_t asn1_value_param = validate_any_fl_impl

(* The ANY validator *)

fn validate_any_impl
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: bool
  ensures pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (LPS.validator_postcond #asn1_strong_parser_kind parse_asn1_value offset v off res))
{
  LPS.validate_ext (RV.validate_rec_vlgen #asn1_value_param read_header_any validate_any_fl) #asn1_strong_parser_kind parse_asn1_value input poffset
}

inline_for_extraction
let validate_any : LPS.validator #asn1_value #asn1_strong_parser_kind parse_asn1_value = validate_any_impl

(* After the identifier has been read *)

let tconsumed (#k: parser_kind) (#t: Type) (p: tot_parser k t) (b: bytes) : GTot (option nat) =
  consumed #k #t p b

let any_body_node_consumed (id: asn1_any_id_t) (b: bytes)
: Lemma
  (requires (CONSTRUCTED? (MK_ASN1_ID?.f id)))
  (ensures (tconsumed (RV.rec_vlgen_body asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id) b ==
    tconsumed (LowParse.Tot.List.parse_list (RV.parse_rec_vlgen asn1_value_param)) b))
= T.parse_synth_eq (LowParse.Tot.List.parse_list (RV.parse_rec_vlgen asn1_value_param)) (RV.RNode #asn1_value #asn1_octetstring_t) b

let any_body_leaf_consumed (id: asn1_any_id_t) (b: bytes)
: Lemma
  (requires (PRIMITIVE? (MK_ASN1_ID?.f id)))
  (ensures (tconsumed (RV.rec_vlgen_body asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id) b ==
    tconsumed (parse_asn1_any_leaf id) b))
= T.parse_synth_eq (parse_asn1_any_leaf id) (RV.RLeaf #asn1_value #asn1_octetstring_t) b

(* A C function of its own: the branches capture [id], and C has no closures *)
fn validate_any_body_impl
  (id: asn1_any_id_t)
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: bool
  ensures pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (LPS.validator_postcond #(RV.rec_vlgen_body_kind asn1_value_param.RV.tag_kind.parser_kind_injective) (RV.rec_vlgen_body asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id) offset v off res))
{
  let p = Ghost.hide (RV.rec_vlgen_body asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id);
  if (CONSTRUCTED? (MK_ASN1_ID?.f id)) {
    Classical.forall_intro (Classical.move_requires (any_body_node_consumed id));
    validate_ext_consumed
      (LPS.validate_ext (PPL.validate_list (RV.validate_rec_vlgen #asn1_value_param read_header_any validate_any_fl) ()) #(LowParse.Spec.List.parse_list_kind (RV.rec_vlgen_kind asn1_value_param).parser_kind_injective) (LowParse.Tot.List.parse_list (RV.parse_rec_vlgen asn1_value_param)))
      #_ #(RV.rec_vlgen_body_kind asn1_value_param.RV.tag_kind.parser_kind_injective) (RV.rec_vlgen_body asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id) input poffset
  } else {
    Classical.forall_intro (Classical.move_requires (any_body_leaf_consumed id));
    validate_ext_consumed #_ #asn1_weak_parser_kind #_ (validate_any_leaf id) #_ #(RV.rec_vlgen_body_kind asn1_value_param.RV.tag_kind.parser_kind_injective) (RV.rec_vlgen_body asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id) input poffset
  }
}

inline_for_extraction
let validate_any_body (id: asn1_any_id_t)
: LPS.validator #_ #(RV.rec_vlgen_body_kind asn1_value_param.RV.tag_kind.parser_kind_injective) (RV.rec_vlgen_body asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id)
= validate_any_body_impl id

let any_body_kind : parser_kind = RV.rec_vlgen_body_kind asn1_value_param.RV.tag_kind.parser_kind_injective

let any_twin_vl (id: asn1_any_id_t) : SB.parser (SVG.parse_vlgen_weak_kind (SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) 0 ILC.asn1_length_max any_body_kind.parser_kind_injective) (RV.rec_vlgen_payload asn1_value asn1_octetstring_t) =
  SVG.parse_vlgen_weak 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max) (SDER.parse_bounded_der_length32 0 ILC.asn1_length_max) #any_body_kind (RV.rec_vlgen_body asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id)

let any_twin_consumed (id: asn1_any_id_t) (b: bytes)
: Lemma
  (tconsumed (parse_asn1_value_twin id) b == consumed (any_twin_vl id) b)
= T.parse_synth_eq (RV.rec_vlgen_payload_parser asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id) (synth_asn1_value_twin id) b;
  ILC.lc_eq #any_body_kind (RV.rec_vlgen_body asn1_value_param (RV.parse_rec_vlgen asn1_value_param) id) b

inline_for_extraction
let validate_any_twin_vl (id: asn1_any_id_t) : LPS.validator (any_twin_vl id) =
  PPVG.validate_vlgen_weak 0 ILC.asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 ILC.asn1_length_max)
    (validate_of_vreader ILC.vread_length) (leaf_read_of_vreader ILC.vread_length)
    #any_body_kind (validate_any_body id) ()

fn validate_any_twin_impl
  (id: asn1_id_t)
  (input: S.slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: bool
  ensures pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (LPS.validator_postcond #asn1_strong_parser_kind (parse_asn1_value_twin id) offset v off res))
{
  if (any_id_valid_impl id) {
    Classical.forall_intro (any_twin_consumed id);
    validate_ext_consumed (validate_any_twin_vl id) #_ #asn1_strong_parser_kind (parse_asn1_value_twin id) input poffset
  } else {
    false
  }
}

inline_for_extraction
let validate_any_twin (id: asn1_id_t) : LPS.validator #asn1_value #asn1_strong_parser_kind (parse_asn1_value_twin id) =
  validate_any_twin_impl id
