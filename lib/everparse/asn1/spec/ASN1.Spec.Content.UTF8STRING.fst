module ASN1.Spec.Content.UTF8STRING

open LowParse.Tot.Combinators
open LowParse.Tot.SeqBytes

open ASN1.Base

let parse_asn1_utf8string : asn1_weak_parser asn1_utf8string_t
= weaken _ (parse_seq_all_bytes `parse_filter` LowParse.Spec.UTF8.correct)
