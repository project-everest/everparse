module ASN1.Pulse.Terminal
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.PulseParse.VReader
open LowParse.Tot.Base
open ASN1.Base
open ASN1.Spec.Content.BOOLEAN
open ASN1.Spec.Content.OCTETSTRING
open ASN1.Spec.Interpreter

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module SCmp = LowParse.Pulse.SizeComparison
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module LPS = LowParse.Pulse.Base
module PPB = LowParse.PulseParse.Base
module LSB = LowParse.Pulse.SeqBytes
module LPI = LowParse.Pulse.Int
module I = ASN1.Pulse.Identifier
module C = ASN1.Pulse.Checkers
module T = LowParse.Tot.Combinators

(* BOOLEAN *)

inline_for_extraction
fn vread_boolean (_: unit)
: vreader #asn1_boolean_t #parse_asn1_boolean_t_kind parse_asn1_boolean
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  lemma_parse_asn1_boolean_unfold (Seq.slice v (SZ.v offset) (Seq.length v));
  let r = I.vread_u8 input poffset;
  match r {
    None -> {
      None #asn1_boolean_t
    }
    Some x -> {
      if (is_valid_asn1_boolean x) {
        Some (decode_asn1_boolean x)
      } else {
        None #asn1_boolean_t
      }
    }
  }
}

inline_for_extraction
let validate_boolean
: LPS.validator #asn1_boolean_t #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_BOOLEAN)
= LPS.validate_ext
    #_ #asn1_weak_parser_kind
    (validate_of_vreader (vread_weaken asn1_weak_parser_kind (vread_boolean ()) ()))
    #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_BOOLEAN)

inline_for_extraction
let read_boolean
: PPB.leaf_reader #asn1_boolean_t #parse_asn1_boolean_t_kind parse_asn1_boolean
= leaf_read_of_vreader (vread_boolean ())

(* BOOLEAN filtered by a predicate (restrictions, DEFAULT) *)
inline_for_extraction
let validate_boolean_filter (f: asn1_boolean_t -> bool)
: LPS.validator
    #(T.parse_filter_refine f)
    #(LowParse.Spec.Combinators.parse_filter_kind asn1_weak_parser_kind)
    (T.parse_filter (asn1_terminal_as_parser ASN1_BOOLEAN) f)
= Classical.forall_intro (T.parse_filter_eq #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_BOOLEAN) f);
  LPS.validate_ext
    #_ #(LowParse.Spec.Combinators.parse_filter_kind asn1_weak_parser_kind)
    (validate_of_vreader (vread_filter (vread_weaken asn1_weak_parser_kind (vread_boolean ()) ()) f))
    #(LowParse.Spec.Combinators.parse_filter_kind asn1_weak_parser_kind)
    (T.parse_filter (asn1_terminal_as_parser ASN1_BOOLEAN) f)

(* OCTET STRING *)

inline_for_extraction
let validate_octetstring
: LPS.validator #asn1_octetstring_t #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_OCTETSTRING)
= LPS.validate_ext
    #_ #asn1_weak_parser_kind
    (LPS.validate_weaken asn1_weak_parser_kind (LSB.validate_seq_all_bytes ()))
    #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_OCTETSTRING)

(* INTEGER (bounded): the content is the whole input. The bound is a
   64-bit integer, compared without assuming anything about the width
   of size_t beyond 16 bits *)

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_integer
  (bound: U64.t { U64.v bound > 0 /\ U64.v bound < 18446744073709551615 })
: LPS.validator #(asn1_terminal_t (ASN1_INTEGER (U64.v bound))) #asn1_weak_parser_kind (asn1_terminal_as_parser (ASN1_INTEGER (U64.v bound)))
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  let off = !poffset;
  pts_to_len input;
  let len = S.len input;
  let n = SZ.sub len off;
  let big = SCmp.u64_lte_sizet (U64.add bound 1UL) n;
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

(* NULL *)

inline_for_extraction
let validate_null
: LPS.validator #(asn1_terminal_t ASN1_NULL) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_NULL)
= LPS.validate_ext
    #_ #_
    (LPS.validate_weaken asn1_weak_parser_kind LowParse.Pulse.Combinators.validate_empty)
    #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_NULL)

(* Raw-bytes string types *)

inline_for_extraction
let validate_raw_string (k: asn1_terminal_k {
  k == ASN1_TELETEXSTRING \/ k == ASN1_VIDEOTEXSTRING \/ k == ASN1_GRAPHICSTRING \/
  k == ASN1_GENERALSTRING \/ k == ASN1_OBJECTDESCRIPTOR
})
: LPS.validator #(asn1_terminal_t k) #asn1_weak_parser_kind (asn1_terminal_as_parser k)
= LPS.validate_ext
    #_ #asn1_weak_parser_kind
    (LPS.validate_weaken asn1_weak_parser_kind (LSB.validate_seq_all_bytes ()))
    #asn1_weak_parser_kind (asn1_terminal_as_parser k)

(* Whole-content byte strings filtered by a predicate *)

let all_bytes_pred (#k: parser_kind) (#t: Type) (p: parser k t) (f: bytes -> GTot bool) : prop =
  forall (b: bytes) . match parse p b with
  | None -> f b == false
  | Some (_, n) -> f b == true /\ n == Seq.length b

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_all_bytes_pred
  (#t: Type0)
  (#k: Ghost.erased parser_kind)
  (p: parser k t)
  (f: Ghost.erased (bytes -> GTot bool))
  (c: C.slice_checker f)
  (sq: squash (all_bytes_pred p f))
: LPS.validator #t #k p
=
  (input: slice byte)
  (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
{
  pts_to_len input;
  let off = !poffset;
  let len = S.len input;
  let s1, s2 = S.split input off;
  let r = c s2;
  S.join s1 s2 input;
  Seq.lemma_split v (SZ.v off);
  if (r) {
    poffset := len;
    true
  } else {
    false
  }
}

#pop-options

let utf8_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_UTF8STRING) LowParse.Spec.UTF8.correct)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes LowParse.Spec.UTF8.correct)

inline_for_extraction
let validate_utf8
: LPS.validator #(asn1_terminal_t ASN1_UTF8STRING) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_UTF8STRING)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_UTF8STRING) LowParse.Spec.UTF8.correct C.check_utf8 (utf8_pred ())

let bmp_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_BMPSTRING) is_valid_bmp)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes is_valid_bmp)

inline_for_extraction
let validate_bmp
: LPS.validator #(asn1_terminal_t ASN1_BMPSTRING) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_BMPSTRING)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_BMPSTRING) is_valid_bmp C.check_bmp (bmp_pred ())

let universal_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_UNIVERSALSTRING) is_valid_universal)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes is_valid_universal)

inline_for_extraction
let validate_universal
: LPS.validator #(asn1_terminal_t ASN1_UNIVERSALSTRING) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_UNIVERSALSTRING)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_UNIVERSALSTRING) is_valid_universal C.check_universal (universal_pred ())

let oid_iri_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_OID_IRI) ASN1.Spec.IRI.is_valid_oid_iri)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes ASN1.Spec.IRI.is_valid_oid_iri)

inline_for_extraction
let validate_oid_iri
: LPS.validator #(asn1_terminal_t ASN1_OID_IRI) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_OID_IRI)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_OID_IRI) ASN1.Spec.IRI.is_valid_oid_iri C.check_oid_iri (oid_iri_pred ())

let relative_oid_iri_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_RELATIVE_OID_IRI) ASN1.Spec.IRI.is_valid_relative_oid_iri)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes ASN1.Spec.IRI.is_valid_relative_oid_iri)

inline_for_extraction
let validate_relative_oid_iri
: LPS.validator #(asn1_terminal_t ASN1_RELATIVE_OID_IRI) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_RELATIVE_OID_IRI)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_RELATIVE_OID_IRI) ASN1.Spec.IRI.is_valid_relative_oid_iri C.check_relative_oid_iri (relative_oid_iri_pred ())

let utctime_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_UTCTIME) ASN1.Spec.Time.is_valid_ASN1UTCTIME)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes ASN1.Spec.Time.is_valid_ASN1UTCTIME)

inline_for_extraction
let validate_utctime
: LPS.validator #(asn1_terminal_t ASN1_UTCTIME) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_UTCTIME)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_UTCTIME) ASN1.Spec.Time.is_valid_ASN1UTCTIME C.check_utctime (utctime_pred ())

let generalizedtime_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_GENERALIZEDTIME) ASN1.Spec.Time.is_valid_ASN1GENERALIZEDTIME)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes ASN1.Spec.Time.is_valid_ASN1GENERALIZEDTIME)

inline_for_extraction
let validate_generalizedtime
: LPS.validator #(asn1_terminal_t ASN1_GENERALIZEDTIME) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_GENERALIZEDTIME)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_GENERALIZEDTIME) ASN1.Spec.Time.is_valid_ASN1GENERALIZEDTIME C.check_generalizedtime (generalizedtime_pred ())

let date_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_DATE) ASN1.Spec.Time.is_valid_ASN1DATE)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes ASN1.Spec.Time.is_valid_ASN1DATE)

inline_for_extraction
let validate_date
: LPS.validator #(asn1_terminal_t ASN1_DATE) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_DATE)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_DATE) ASN1.Spec.Time.is_valid_ASN1DATE C.check_date (date_pred ())

let timeofday_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_TIME_OF_DAY) ASN1.Spec.Time.is_valid_ASN1TIMEOFDAY)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes ASN1.Spec.Time.is_valid_ASN1TIMEOFDAY)

inline_for_extraction
let validate_timeofday
: LPS.validator #(asn1_terminal_t ASN1_TIME_OF_DAY) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_TIME_OF_DAY)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_TIME_OF_DAY) ASN1.Spec.Time.is_valid_ASN1TIMEOFDAY C.check_timeofday (timeofday_pred ())

let datetime_pred () : Lemma (all_bytes_pred (asn1_terminal_as_parser ASN1_DATE_TIME) ASN1.Spec.Time.is_valid_ASN1DATETIME)
= Classical.forall_intro (T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes ASN1.Spec.Time.is_valid_ASN1DATETIME)

inline_for_extraction
let validate_datetime
: LPS.validator #(asn1_terminal_t ASN1_DATE_TIME) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_DATE_TIME)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_DATE_TIME) ASN1.Spec.Time.is_valid_ASN1DATETIME C.check_datetime (datetime_pred ())

(* Character strings: lists of filtered bytes *)

inline_for_extraction
let validate_char_list (f: U8.t -> bool) (f': (x: U8.t) -> (y: bool { y == f x }))
: LPS.validator #_ #(LowParse.Spec.List.parse_list_kind (LowParse.Spec.Combinators.parse_filter_kind LowParse.Spec.Int.parse_u8_kind).parser_kind_injective) (LowParse.Tot.List.parse_list (T.parse_filter LowParse.Tot.Int.parse_u8 f))
= LPS.validate_ext
    (LowParse.PulseParse.List.validate_list
      (LPS.validate_ext
        (LowParse.PulseParse.Combinators.validate_filter LPI.validate_u8 (PPB.leaf_reader_of_serialized (LPI.read_u8' ())) f f' ())
        #(LowParse.Spec.Combinators.parse_filter_kind LowParse.Spec.Int.parse_u8_kind)
        (T.parse_filter LowParse.Tot.Int.parse_u8 f))
      ())
    (LowParse.Tot.List.parse_list (T.parse_filter LowParse.Tot.Int.parse_u8 f))

(* Machine-integer versions of the character predicates of ASN1.Base *)

inline_for_extraction
let is_ia5_char_impl (c: U8.t) : Tot (b: bool { b == is_ia5_char c }) = U8.lt c 128uy

inline_for_extraction
let is_numeric_char_impl (c: U8.t) : Tot (b: bool { b == is_numeric_char c }) =
  (U8.lte 48uy c && U8.lte c 57uy) || c = 32uy

inline_for_extraction
let is_visible_char_impl (c: U8.t) : Tot (b: bool { b == is_visible_char c }) =
  U8.lte 32uy c && U8.lte c 126uy

inline_for_extraction
let is_printable_char_impl (c: U8.t) : Tot (b: bool { b == is_printable_char c }) =
  (U8.lte 65uy c && U8.lte c 90uy) ||
  (U8.lte 97uy c && U8.lte c 122uy) ||
  (U8.lte 48uy c && U8.lte c 57uy) ||
  c = 32uy ||
  (U8.lte 39uy c && U8.lte c 41uy) ||
  (U8.lte 43uy c && U8.lte c 47uy) ||
  c = 58uy || c = 61uy || c = 63uy

inline_for_extraction
let validate_ia5
: LPS.validator #(asn1_terminal_t ASN1_IA5STRING) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_IA5STRING)
= LPS.validate_ext #_ #_ (LPS.validate_weaken asn1_weak_parser_kind (validate_char_list is_ia5_char is_ia5_char_impl)) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_IA5STRING)

inline_for_extraction
let validate_numeric
: LPS.validator #(asn1_terminal_t ASN1_NUMERICSTRING) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_NUMERICSTRING)
= LPS.validate_ext #_ #_ (LPS.validate_weaken asn1_weak_parser_kind (validate_char_list is_numeric_char is_numeric_char_impl)) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_NUMERICSTRING)

inline_for_extraction
let validate_printable
: LPS.validator #(asn1_terminal_t ASN1_PRINTABLESTRING) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_PRINTABLESTRING)
= LPS.validate_ext #_ #_ (LPS.validate_weaken asn1_weak_parser_kind (validate_char_list is_printable_char is_printable_char_impl)) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_PRINTABLESTRING)

inline_for_extraction
let validate_visible
: LPS.validator #(asn1_terminal_t ASN1_VISIBLESTRING) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_VISIBLESTRING)
= LPS.validate_ext #_ #_ (LPS.validate_weaken asn1_weak_parser_kind (validate_char_list is_visible_char is_visible_char_impl)) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_VISIBLESTRING)

(* BIT STRING *)

#push-options "--z3rlimit 64 --ifuel 2"

let bitstring_payload_eq (u: U8.t {U8.v u <= 7}) (b': bytes)
: Lemma (match parse (ASN1.Spec.Content.BITSTRING.parse_asn1_bitstring_payload u) b' with
  | None -> ASN1.Spec.Content.BITSTRING.filter_asn1_bitstring_payload u b' == false
  | Some (_, n) -> ASN1.Spec.Content.BITSTRING.filter_asn1_bitstring_payload u b' == true /\ n == Seq.length b')
= let open ASN1.Spec.Content.BITSTRING in
  T.parse_synth_eq (LowParse.Tot.SeqBytes.parse_seq_all_bytes `T.parse_filter` filter_asn1_bitstring_payload u) (synth_asn1_bitstring u) b';
  T.parse_filter_eq LowParse.Tot.SeqBytes.parse_seq_all_bytes (filter_asn1_bitstring_payload u) b';
  assert (parse LowParse.Tot.SeqBytes.parse_seq_all_bytes b' == Some (b', Seq.length b'))

let bitstring_eq (b: bytes)
: Lemma (match parse (asn1_terminal_as_parser ASN1_BITSTRING) b with
  | None -> C.bitstring_ok b == false
  | Some (_, n) -> C.bitstring_ok b == true /\ n == Seq.length b)
= let open ASN1.Spec.Content.BITSTRING in
  parse_asn1_bitstring_payload_cases_injective ();
  T.and_then_eq (LowParse.Tot.Int.parse_u8 `T.parse_filter` filter_asn1_bitstring_unused) parse_asn1_bitstring_payload b;
  T.parse_filter_eq LowParse.Tot.Int.parse_u8 filter_asn1_bitstring_unused b;
  LowParse.Spec.Base.parser_kind_prop_equiv LowParse.Spec.Int.parse_u8_kind LowParse.Spec.Int.parse_u8;
  if Seq.length b > 0
  then begin
    LowParse.Spec.Int.parse_u8_spec' b;
    let u = Seq.index b 0 in
    if filter_asn1_bitstring_unused u
    then bitstring_payload_eq u (Seq.slice b 1 (Seq.length b))
  end

#pop-options

inline_for_extraction
let validate_bitstring
: LPS.validator #(asn1_terminal_t ASN1_BITSTRING) #asn1_weak_parser_kind (asn1_terminal_as_parser ASN1_BITSTRING)
= validate_all_bytes_pred (asn1_terminal_as_parser ASN1_BITSTRING) C.bitstring_ok C.check_bitstring (Classical.forall_intro bitstring_eq)
