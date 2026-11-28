module ASN1.Spec.Content.NULL

open ASN1.Base

open LowParse.Tot.Combinators

let parse_asn1_null : asn1_weak_parser asn1_null_t
= weaken _ parse_empty
