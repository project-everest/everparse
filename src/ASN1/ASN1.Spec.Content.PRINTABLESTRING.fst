module ASN1.Spec.Content.PRINTABLESTRING

open ASN1.Base

open LowParse.Spec.Combinators
open LowParse.Spec.Int
open LowParse.Spec.List

module U8 = FStar.UInt8

let parse_printable_char =
  parse_u8 `parse_filter` is_printable_char

let parse_asn1_printablestring : asn1_weak_parser asn1_printablestring_t =
  weaken _ (parse_list parse_printable_char)
  
