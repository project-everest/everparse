module ASN1.Low.IdentifierU32

open ASN1.Base

open ASN1.Spec.IdentifierU32

open LowParse.Low.Combinators

module U8 = FStar.UInt8
module HST = FStar.HyperStack.ST

inline_for_extraction
let validate_asn1_identifier_tail (state : asn1_partial_id_t) (buf : byte)
: Tot (validator (parse_asn1_identifier_tail state buf))
= fun #rrel #rel (input: slice rrel rel) pos ->
  let h = HST.get() in
    let _ =
      valid_equiv (parse_asn1_identifier_tail state buf) h input (uint64_to_uint32 pos)
    in
  if U8.lt (buf) (U8.uint_to_t 128) then
    pos
  else
    validator_error_generic
  
inline_for_extraction
let validate_asn1_identifieru21 ()
: Tot (validator parse_asn1_identifier_u21)
= admit ()

inline_for_extraction
let read_asn1_identifieru21 ()
: Tot (leaf_reader parse_asn1_identifier_u21)
= admit ()

