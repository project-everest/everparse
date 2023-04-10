module ASN1.Low.LengthU32

open ASN1.Spec.LengthU32
open LowParse.Low.Base

module LPDER = LowParse.Low.DER
module U32 = FStar.UInt32

inline_for_extraction
let validate_asn1_lengthu32 () : Tot (validator parse_asn1_length_u32_t)
= LPDER.validate_bounded_der_length32 0 (U32.uint_to_t 0) 4294967295 (U32.uint_to_t 4294967295)

inline_for_extraction
let read_asn1_lengthu32 () : Tot (leaf_reader (parse_asn1_length_u32_t))
= LPDER.read_bounded_der_length32 0 4294967295
