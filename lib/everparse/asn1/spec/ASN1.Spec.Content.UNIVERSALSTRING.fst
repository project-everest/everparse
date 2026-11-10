module ASN1.Spec.Content.UNIVERSALSTRING

open LowParse.Tot.Combinators
open LowParse.Tot.SeqBytes

open ASN1.Base

let parse_asn1_universalstring : asn1_weak_parser asn1_universalstring_t
= weaken _ (parse_seq_all_bytes `parse_filter` is_valid_universal)
