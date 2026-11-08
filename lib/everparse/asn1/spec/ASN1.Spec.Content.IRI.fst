module ASN1.Spec.Content.IRI

open LowParse.Tot.Combinators
open LowParse.Tot.SeqBytes

open ASN1.Base
open ASN1.Spec.IRI

let parse_asn1_OID_IRI : asn1_weak_parser asn1_oid_iri_t
= weaken _ (parse_seq_all_bytes `parse_filter` is_valid_oid_iri)

let parse_asn1_RELATIVE_OID_IRI : asn1_weak_parser asn1_relative_oid_iri_t
= weaken _ (parse_seq_all_bytes `parse_filter` is_valid_relative_oid_iri)
