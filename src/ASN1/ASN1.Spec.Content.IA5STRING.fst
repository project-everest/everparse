module ASN1.Spec.Content.IA5STRING

open ASN1.Base

open LowParse.Spec.Combinators
open LowParse.Spec.Int
open LowParse.Spec.List

module U8 = FStar.UInt8

let parse_ia5_char =
  parse_u8 `parse_filter` is_ia5_char

let parse_asn1_ia5string : asn1_weak_parser asn1_ia5string_t =
  weaken _ (parse_list parse_ia5_char)
  
