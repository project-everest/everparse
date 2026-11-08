module ASN1.Spec.Content.NUMERICSTRING

open ASN1.Base

open LowParse.Tot.Combinators
open LowParse.Tot.Int
open LowParse.Tot.List

module U8 = FStar.UInt8

let parse_numeric_char =
  parse_u8 `parse_filter` is_numeric_char

let parse_asn1_numericstring : asn1_weak_parser asn1_numericstring_t =
  weaken _ (parse_list parse_numeric_char)
