module ASN1.Bytes

/// The byte-string representation used throughout the ASN.1 specification.
///
/// ASN.1 used to inherit this type from the abstract bytes type of F*'s
/// standard library.  It is now a plain byte sequence, definitionally equal to
/// LowParse's own [bytes], so that LowParse parsers and serializers apply to
/// ASN.1 values without any coercion.
///
/// This module sits below both [ASN1.Spec.Time] and [ASN1.Base], which is why
/// the abbreviation does not live in either of them.

module Seq = FStar.Seq
module U8 = FStar.UInt8

let asn1_bytes = Seq.seq U8.t
