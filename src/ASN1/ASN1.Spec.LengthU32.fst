module ASN1.Spec.LengthU32

open ASN1.Base

include LowParse.Spec.Base
include LowParse.Spec.Combinators

module LPDER = LowParse.Spec.DER

(* Ref: X.690 8.1.3 9.1 10.1 *)

(* Reusing LowParse.Spec.DER *)

let parse_asn1_length_u32_t_kind = LPDER.parse_bounded_der_length32_kind 0 4294967295

let parse_asn1_length_u32_t : parser parse_asn1_length_u32_t_kind asn1_length_u32_t
= LPDER.parse_bounded_der_length32 0 4294967295

let serialize_asn1_length_u32_t : serializer parse_asn1_length_u32_t
= LPDER.serialize_bounded_der_length32 0 4294967295

