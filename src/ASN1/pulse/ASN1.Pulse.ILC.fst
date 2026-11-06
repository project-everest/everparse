module ASN1.Pulse.ILC
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.LengthU32
open ASN1.Spec.ILC

module SZ = FStar.SizeT
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module LPI = LowParse.Pulse.Int
module PPB = LowParse.PulseParse.Base
module PPBI = LowParse.PulseParse.BoundedInt
module PPVG = LowParse.PulseParse.VLGen
module PPDER = LowParse.Pulse.DER
module SDER = LowParse.Spec.DER
module SVG = LowParse.Spec.VLGen
module SC = LowParse.Spec.Combinators
module T = LowParse.Tot.Combinators
module TVG = LowParse.Tot.VLGen
module I = ASN1.Pulse.Identifier

(* Lengths *)

let asn1_length_max = 4294967295

let length_eq (b: bytes)
: Lemma
  (parse parse_asn1_length_u32_t b == parse (SDER.parse_bounded_der_length32 0 asn1_length_max) b)
= ()

inline_for_extraction noextract
let read_u8 : PPB.leaf_reader LowParse.Spec.Int.parse_u8 =
  PPB.leaf_reader_of_serialized (LPI.read_u8' ())

inline_for_extraction noextract
let read_bi_serialized (i: LowParse.Spec.BoundedInt.integer_size)
: LPS.leaf_reader (LowParse.Spec.BoundedInt.serialize_bounded_integer i)
= PPB.serialized_of_leaf_reader _ (PPBI.leaf_read_bounded_integer i)

inline_for_extraction
let validate_length_spec : LPS.validator #(LowParse.Spec.BoundedInt.bounded_int32 0 asn1_length_max) #(SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (SDER.parse_bounded_der_length32 0 asn1_length_max) =
  PPDER.validate_bounded_der_length32 0ul 4294967295ul (LPI.read_u8' ()) read_bi_serialized

inline_for_extraction
let read_length_spec : PPB.leaf_reader #(LowParse.Spec.BoundedInt.bounded_int32 0 asn1_length_max) #(SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (SDER.parse_bounded_der_length32 0 asn1_length_max) =
  PPDER.leaf_read_bounded_der_length32 0 asn1_length_max read_u8 PPBI.leaf_read_bounded_integer

inline_for_extraction
let jump_length_spec : LPS.jumper #(LowParse.Spec.BoundedInt.bounded_int32 0 asn1_length_max) #(SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (SDER.parse_bounded_der_length32 0 asn1_length_max) =
  PPDER.jump_bounded_der_length32 0 asn1_length_max read_u8

(* The length validator and reader, fused, and extracted once as a C
   function shared by every TLV (inlining it costs hundreds of lines of C
   per TLV) *)
fn vread_length_impl
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires pts_to input #pm v ** R.pts_to poffset offset ** pure (SZ.v offset <= Seq.length v)
  returns res: option (LowParse.Spec.BoundedInt.bounded_int32 0 asn1_length_max)
  ensures pts_to input #pm v ** (exists* off . R.pts_to poffset off ** pure (vreader_postcond #(SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (SDER.parse_bounded_der_length32 0 asn1_length_max) offset v off res))
{
  let off = !poffset;
  let ok = validate_length_spec input poffset;
  if ok {
    let off1 = !poffset;
    let x = PPB.read_parsed_from_validator_success read_length_spec input off off1;
    Some x
  } else {
    None
  }
}

inline_for_extraction
let vread_length : vreader #(LowParse.Spec.BoundedInt.bounded_int32 0 asn1_length_max) #(SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (SDER.parse_bounded_der_length32 0 asn1_length_max) =
  vread_length_impl

(* LC: length then contents of exactly that length *)

let lc_eq
  (#k: parser_kind) (#t: Type) (p: parser k t) (b: bytes)
: Lemma
  (parse (TVG.parse_vlgen_weak 0 asn1_length_max parse_asn1_length_u32_t p) b ==
    LowParse.Spec.Base.parse (SVG.parse_vlgen_weak 0 asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (SDER.parse_bounded_der_length32 0 asn1_length_max) #k #t p) b)
= SVG.parse_vlgen_weak_unfold 0 asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (SDER.parse_bounded_der_length32 0 asn1_length_max) #k #t p b

inline_for_extraction
let validate_asn1_LC
  (#ack : Ghost.erased asn1_content_k)
  (#p : asn1_weak_parser (asn1_content_t ack))
  (v: LPS.validator #(asn1_content_t ack) #asn1_weak_parser_kind p)
: LPS.validator (parse_asn1_LC p)
= Classical.forall_intro (lc_eq p);
  LPS.validate_ext
    #_ #(SVG.parse_vlgen_weak_kind (SDER.parse_bounded_der_length32_kind 0 asn1_length_max) 0 asn1_length_max asn1_weak_parser_kind.parser_kind_injective)
    (PPVG.validate_vlgen_weak 0 asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (validate_of_vreader vread_length) (leaf_read_of_vreader vread_length) #asn1_weak_parser_kind v ())
    #asn1_strong_parser_kind (parse_asn1_LC p)

#push-options "--z3rlimit 32"

inline_for_extraction
fn jump_asn1_LC
  (#ack : Ghost.erased asn1_content_k)
  (p : asn1_weak_parser (asn1_content_t ack))
: LPS.jumper #(asn1_content_t ack) #asn1_strong_parser_kind (parse_asn1_LC p)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  lc_eq p sinput;
  SVG.parse_vlgen_weak_unfold 0 asn1_length_max #(SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (SDER.parse_bounded_der_length32 0 asn1_length_max) #asn1_weak_parser_kind #(asn1_content_t ack) p sinput;
  parser_kind_prop_equiv (SDER.parse_bounded_der_length32_kind 0 asn1_length_max) (SDER.parse_bounded_der_length32 0 asn1_length_max);
  let mut poff = offset;
  let r = vread_length input poff;
  let off1 = !poff;
  match r {
    Some len -> {
      pts_to_len input;
      SZ.fits_lte (SZ.v off1 + U32.v len) (Seq.length v);
      SZ.add off1 (SZ.uint32_to_sizet len)
    }
    None -> {
      offset
    }
  }
}

#pop-options

(* ILC: identifier (filtered), then LC *)

let ilc_eq
  (id : asn1_id_t)
  (#ack : asn1_content_k)
  (p : asn1_weak_parser (asn1_content_t ack))
  (b: bytes)
: Lemma
  (parse (parse_asn1_ILC id p) b == (
    match parse parse_asn1_identifier_U32 b with
    | None -> None
    | Some (id', c1) ->
      if id' = id
      then match parse (parse_asn1_LC p) (Seq.slice b c1 (Seq.length b)) with
        | None -> None
        | Some (x, c2) -> Some (x, c1 + c2)
      else None
  ))
= let pf = parse_asn1_identifier_U32 `T.parse_filter` (fun id' -> id' = id) in
  T.parse_synth_eq (pf `T.nondep_then` parse_asn1_LC p) snd b;
  T.nondep_then_eq pf (parse_asn1_LC p) b;
  T.parse_filter_eq parse_asn1_identifier_U32 (fun id' -> id' = id) b

inline_for_extraction
let asn1_id_eq (id1 id2: asn1_id_t) : Tot (b: bool { b == (id1 = id2) }) =
  match id1, id2 with
  | MK_ASN1_ID c1 f1 v1, MK_ASN1_ID c2 f2 v2 -> c1 = c2 && f1 = f2 && v1 = v2

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_asn1_ILC
  (id : asn1_id_t)
  (#ack : Ghost.erased asn1_content_k)
  (#p : asn1_weak_parser (asn1_content_t ack))
  (v: LPS.validator #(asn1_content_t ack) #asn1_weak_parser_kind p)
: LPS.validator #(asn1_content_t ack) #asn1_strong_parser_kind (parse_asn1_ILC id p)
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#vb: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice vb (SZ.v offset) (Seq.length vb));
  ilc_eq id p sinput;
  let r = I.vread_identifier input poffset;
  match r {
    None -> {
      false
    }
    Some id' -> {
      if (asn1_id_eq id' id) {
        with off1 . assert (R.pts_to poffset off1);
        Seq.slice_slice vb (SZ.v offset) (Seq.length vb) (SZ.v off1 - SZ.v offset) (Seq.length vb - SZ.v offset);
        validate_asn1_LC #ack #p v input poffset
      } else {
        false
      }
    }
  }
}

inline_for_extraction
fn jump_asn1_ILC
  (id : asn1_id_t)
  (#ack : Ghost.erased asn1_content_k)
  (p : asn1_weak_parser (asn1_content_t ack))
: LPS.jumper #(asn1_content_t ack) #asn1_strong_parser_kind (parse_asn1_ILC id p)
=
  (input: slice byte)
  (offset: SZ.t)
  (#pm: perm)
  (#vb: Ghost.erased bytes)
{
  let sinput = Ghost.hide (Seq.slice vb (SZ.v offset) (Seq.length vb));
  ilc_eq id p sinput;
  let off1 = I.jump_identifier input offset;
  Seq.slice_slice vb (SZ.v offset) (Seq.length vb) (SZ.v off1 - SZ.v offset) (Seq.length vb - SZ.v offset);
  jump_asn1_LC #ack p input off1
}

#pop-options
