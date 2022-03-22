module ASN1.Low.ILC

include ASN1.Base

include ASN1.Spec.ILC
include ASN1.Low.LengthU32
include ASN1.Low.IdentifierU32

include LowParse.Low.Combinators
include LowParse.Low.VLGen

module U32 = FStar.UInt32

inline_for_extraction
let validate_asn1_LC 
  (#k : asn1_content_k) 
  (#p : asn1_weak_parser (asn1_content_t k))
  (v : validator p)
: Tot (validator (parse_asn1_LC p))
= validate_weaken _  
  (validate_vlgen_weak 0 (U32.uint_to_t 0) 4294967295 (U32.uint_to_t 4294967295) (validate_asn1_lengthu32 ()) (read_asn1_lengthu32 ()) v) ()

(*
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
*)

inline_for_extraction
let validate_asn1_ILC
  (id : asn1_id_t)
  (#k : asn1_content_k)
  (#p : asn1_weak_parser (asn1_content_t k))
  (v : validator p)
: Tot (validator (parse_asn1_ILC id p))
= let v' =
    validate_synth
    (validate_filter (validate_asn1_identifieru21 ()) (read_asn1_identifieru21 ()) (fun id' -> id' = id) (fun id' -> id' = id)
    `validate_nondep_then`
    validate_asn1_LC v)
    (snd)
    _
  in
  validate_weaken _ v' ()
