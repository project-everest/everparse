module ASN1.Spec.Content.BOOLEAN

open ASN1.Base

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.Int

module U8 = FStar.UInt8

let byte = U8.t

(* Ref: X.690 8.2 and 11.1 *)

inline_for_extraction
let asn1_boolean_TRUE_DER : byte = 0xFFuy

inline_for_extraction
let asn1_boolean_FALSE_DER : byte = 0x00uy

let is_valid_asn1_boolean (b : byte)
= b = asn1_boolean_TRUE_DER || b = asn1_boolean_FALSE_DER

let decode_asn1_boolean (b : parse_filter_refine is_valid_asn1_boolean) : asn1_boolean_t
= b = asn1_boolean_TRUE_DER

let encode_asn1_boolean (b : asn1_boolean_t) : parse_filter_refine is_valid_asn1_boolean
= match b with
  | true -> asn1_boolean_TRUE_DER
  | false -> asn1_boolean_FALSE_DER

let parse_asn1_boolean_t_kind = strong_parser_kind 1 1 None

let parse_asn1_boolean : parser parse_asn1_boolean_t_kind asn1_boolean_t
=  parse_u8
  `parse_filter`
  is_valid_asn1_boolean
  `parse_synth`
  decode_asn1_boolean

let lemma_parse_asn1_boolean_unfold input :
  Lemma (parse parse_asn1_boolean input ==
  (match parse parse_u8 input with
   | Some (x, consumed) -> if is_valid_asn1_boolean x then
                           Some (decode_asn1_boolean x, consumed)
                         else
                           None
   | None -> None))
= parser_kind_prop_equiv asn1_weak_parser_kind parse_asn1_boolean;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  if Seq.length input > 0 then
  (parse_u8_spec input;
   parse_u8_spec' input);
  parse_filter_eq
    (parse_u8)
    (is_valid_asn1_boolean)
    (input);
  parse_synth_eq
    (parse_u8
     `parse_filter`
     is_valid_asn1_boolean)
    (decode_asn1_boolean)
    (input)    

let serialize_asn1_boolean : serializer parse_asn1_boolean
= serialize_synth
    (parse_u8 `parse_filter` is_valid_asn1_boolean)
    (decode_asn1_boolean)
    (serialize_u8 `serialize_filter` is_valid_asn1_boolean)
    (encode_asn1_boolean)
    ()

