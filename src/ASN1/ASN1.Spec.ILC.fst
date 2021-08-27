module ASN1.Spec.ILC

open ASN1.Base

include ASN1.Spec.IdentifierU32
include ASN1.Spec.LengthU32

include LowParse.Spec.Base
include LowParse.Spec.Combinators
include LowParse.Spec.VLGen

module U32 = FStar.UInt32
module Seq = FStar.Seq

let parse_asn1_LC_kind (k: parser_kind) = parse_bounded_vlgen_kind (parse_asn1_length_u32_t_kind) 0 4294967295 k

let parse_asn1_LC 
  (#ack : asn1_content_k)
  (#k : parser_kind)
  (#p : parser k (asn1_content_t ack))
  (s : serializer p { parse_vlgen_precond 0 4294967295 k })
: parser (parse_asn1_LC_kind k) (asn1_content_t ack)
= parse_bounded_vlgen 0 4294967295 parse_asn1_length_u32_t s
  `parse_synth`
  (synth_vlgen 0 4294967295 s)

let parse_asn1_ILC_kind (k : parser_kind) = and_then_kind parse_asn1_identifier_u21_kind (parse_asn1_LC_kind k)

let parse_asn1_ILC
  (id : asn1_id_t)
  (#ack : asn1_content_k)
  (#k : parser_kind)
  (#p : parser k (asn1_content_t ack))
  (s : serializer p { parse_vlgen_precond 0 4294967295 k })
: parser (parse_asn1_ILC_kind k) (asn1_content_t ack)
= parse_asn1_identifier_u21
  `parse_filter`
  (fun id' -> id' = id)
  `nondep_then`
  parse_asn1_LC s
  `parse_synth`
  (snd)
