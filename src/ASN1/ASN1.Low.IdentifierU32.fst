module ASN1.Low.IdentifierU32

include ASN1.Base

include ASN1.Spec.IdentifierU32

include LowParse.Low.Combinators

inline_for_extraction
let validate_asn1_identifieru21 ()
: Tot (validator parse_asn1_identifier_u21)
= admit ()

inline_for_extraction
let read_asn1_identifieru21 ()
: Tot (leaf_reader parse_asn1_identifier_u21)
= admit ()
