module ASN1.Spec.Content.VISIBLESTRING

open ASN1.Base

open LowParse.Tot.Combinators
open LowParse.Tot.Int
open LowParse.Tot.List

let parse_visible_char =
  parse_u8 `parse_filter` is_visible_char

let parse_asn1_visiblestring : asn1_weak_parser asn1_visiblestring_t =
  weaken _ (parse_list parse_visible_char)
