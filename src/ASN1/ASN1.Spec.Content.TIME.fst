module ASN1.Spec.Content.TIME

open LowParse.Tot.Combinators
open LowParse.Tot.Bytes

open ASN1.Base
open ASN1.Spec.Time

(* Warning: Temporary Solutions *)

let parse_asn1_UTCTIME : asn1_weak_parser asn1_utctime_t
= weaken _ (parse_all_bytes `parse_filter` is_valid_ASN1UTCTIME)

let parse_asn1_GENERALIZEDTIME : asn1_weak_parser asn1_generalizedtime_t
= weaken _ (parse_all_bytes `parse_filter` is_valid_ASN1GENERALIZEDTIME)

