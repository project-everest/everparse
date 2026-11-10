module ASN1.Spec.IRI

(* Validity of OID-IRI and RELATIVE-OID-IRI values (X.680 34, 35; X.690
   8.21, 8.22): their contents are the UTF-8 encoding of a "/"-separated list
   of Unicode labels (X.660 7.5). A label is either an integer Unicode label
   (decimal digits, without leading zeros), or a non-integer Unicode label made
   of letters, digits, "-", ".", "_", "~" (RFC 3987 iunreserved) and non-ASCII
   characters.

   Approximation: non-ASCII characters are only required to be valid UTF-8;
   their membership in the RFC 3987 ucschar ranges and the X.660 restrictions
   on hyphens are not checked. *)

open ASN1.Bytes

module U8 = FStar.UInt8
module Seq = FStar.Seq

let is_iri_digit (c : U8.t) : bool =
  48 <= U8.v c && U8.v c <= 57 // 0 - 9

let is_iri_label_char (c : U8.t) : bool =
  let v = U8.v c in
  v >= 128 ||                // non-ASCII (UTF-8 multibyte sequence)
  (65 <= v && v <= 90) ||    // A - Z
  (97 <= v && v <= 122) ||   // a - z
  is_iri_digit c ||
  v = 45 || v = 46 || v = 95 || v = 126 // - . _ ~

let iri_slash : U8.t = 47uy

(* The labels of `b` from position `i`, the current label having started at
   `start`; `digits` is whether the current label is made of digits only *)
let rec iri_labels_ok
  (b : asn1_bytes)
  (start : nat)
  (i : nat {start <= i /\ i <= Seq.length b})
  (digits : bool)
: Tot bool (decreases (Seq.length b - i))
= if i = Seq.length b || Seq.index b i = iri_slash
  then
    (* the label is non-empty, and an integer label has no leading zero *)
    i > start &&
    (not digits || i = start + 1 || Seq.index b start <> 48uy) &&
    (i = Seq.length b || iri_labels_ok b (i + 1) (i + 1) true)
  else
    is_iri_label_char (Seq.index b i) &&
    iri_labels_ok b start (i + 1) (digits && is_iri_digit (Seq.index b i))

let is_valid_relative_oid_iri (b : asn1_bytes) : bool =
  LowParse.Spec.UTF8.correct b &&
  iri_labels_ok b 0 0 true

let is_valid_oid_iri (b : asn1_bytes) : bool =
  LowParse.Spec.UTF8.correct b &&
  Seq.length b > 0 &&
  Seq.index b 0 = iri_slash &&
  iri_labels_ok b 1 1 true
