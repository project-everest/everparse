module ASN1.Spec.ILC

open ASN1.Base

open ASN1.Spec.IdentifierU32
open ASN1.Spec.LengthU32

open LowParse.Spec.Base
open LowParse.Spec.Combinators
open LowParse.Spec.VLGen

module U32 = FStar.UInt32
module Seq = FStar.Seq

let parse_asn1_LC 
  (#ack : asn1_content_k)
  (p : asn1_weak_parser (asn1_content_t ack))
: asn1_strong_parser (asn1_content_t ack)
= weaken _ (parse_vlgen_weak 0 4294967295 parse_asn1_length_u32_t p)

let parse_asn1_ILC
  (id : asn1_id_t)
  (#ack : asn1_content_k)
  (p : asn1_weak_parser (asn1_content_t ack))
: asn1_strong_parser (asn1_content_t ack)
= let p' = 
    parse_asn1_identifier_u21
    `parse_filter`
    (fun id' -> id' = id)
    `nondep_then`
    parse_asn1_LC p
    `parse_synth`
    (snd) in
  weaken asn1_strong_parser_kind p'

let parse_asn1_ILC_twin
  (id : asn1_id_t)
  (#ack : asn1_content_k)
  (p : asn1_weak_parser (asn1_content_t ack))
  (id' : asn1_id_t)
: asn1_strong_parser (asn1_content_t ack)
= if (id = id') then
     parse_asn1_LC p
  else
     fail_parser _ _

let parser_asn1_ILC_twin_case_injective
  (id : asn1_id_t)
  (#ack : asn1_content_k)
  (p : asn1_weak_parser (asn1_content_t ack))
: Lemma
  (and_then_cases_injective (parse_asn1_ILC_twin id p))
= and_then_cases_injective_intro (parse_asn1_ILC_twin id p) (fun id1 id2 _ _ -> assert (id1 = id) ; assert (id2 = id))

(*

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

let parse_asn1_ILC_twin
  (id : asn1_id_t)
  (#ack : asn1_content_k)
  (#k : parser_kind)
  (#p : parser k (asn1_content_t ack))
  (s : serializer p { parse_vlgen_precond 0 4294967295 k })
  (id' : asn1_id_t)
: parser (parse_asn1_LC_kind k) (asn1_content_t ack)
= if (id = id') then
     parse_asn1_LC s
  else
     fail_parser _ _

let parser_asn1_ILC_twin_case_injective
  (id : asn1_id_t)
  (#ack : asn1_content_k)
  (#k : parser_kind)
  (#p : parser k (asn1_content_t ack))
  (s : serializer p { parse_vlgen_precond 0 4294967295 k })
: Lemma
  (and_then_cases_injective (parse_asn1_ILC_twin id s))
= and_then_cases_injective_intro (parse_asn1_ILC_twin id s) (fun id1 id2 _ _ -> assert (id1 = id) ; assert (id2 = id))
*)
