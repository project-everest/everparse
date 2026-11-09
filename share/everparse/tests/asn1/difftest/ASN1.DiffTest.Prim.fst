module ASN1.DiffTest.Prim

(* Differential testing (difftest/): primitive universal types.
   Must agree with difftest/schemas/{DiffPrim,DiffRelOid,DiffDesc,DiffIRI}.asn *)

open ASN1.Base
open ASN1.Syntax

let bool_ = asn1_boolean
let int_ = asn1_integer
(* Enum ::= ENUMERATED { a(0), b(1), c(5) } *)
let enum_ = asn1_enumerated [0; 1; 5]
let bits = asn1_bitstring
let octets = asn1_octetstring
let null_ = asn1_null
let oid = asn1_oid
let relOid = asn1_relative_oid
let desc = asn1_objectdescriptor
let iri = asn1_oid_iri
let relIri = asn1_relative_oid_iri
