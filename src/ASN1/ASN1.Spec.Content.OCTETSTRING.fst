module ASN1.Spec.Content.OCTETSTRING

open ASN1.Base

include LowParse.Tot.Bytes

let parse_asn1_octetstring : asn1_weak_parser asn1_octetstring_t 
= weaken _ parse_all_bytes
