module ASN1.Spec.Content.TIME

open LowParse.Tot.Combinators
open LowParse.Tot.SeqBytes

open ASN1.Base
open ASN1.Spec.Time

(* Warning: Temporary Solutions *)

let parse_asn1_UTCTIME : asn1_weak_parser asn1_utctime_t
= weaken _ (parse_seq_all_bytes `parse_filter` is_valid_ASN1UTCTIME)

let parse_asn1_GENERALIZEDTIME : asn1_weak_parser asn1_generalizedtime_t
= weaken _ (parse_seq_all_bytes `parse_filter` is_valid_ASN1GENERALIZEDTIME)


let parse_asn1_DATE : asn1_weak_parser asn1_date_t
= weaken _ (parse_seq_all_bytes `parse_filter` is_valid_ASN1DATE)

let parse_asn1_TIMEOFDAY : asn1_weak_parser asn1_time_of_day_t
= weaken _ (parse_seq_all_bytes `parse_filter` is_valid_ASN1TIMEOFDAY)

let parse_asn1_DATETIME : asn1_weak_parser asn1_date_time_t
= weaken _ (parse_seq_all_bytes `parse_filter` is_valid_ASN1DATETIME)
