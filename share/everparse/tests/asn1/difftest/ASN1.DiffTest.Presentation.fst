module ASN1.DiffTest.Presentation

(* Differential testing (difftest/): EXTERNAL, EMBEDDED PDV, CHARACTER STRING.
   Must agree with difftest/schemas/{DiffExternal,DiffPdv,DiffCharStr}.asn *)

let ext = ASN1.UniversalTypes.asn1_external
let pdv = ASN1.UniversalTypes.asn1_embedded_pdv
let charStr = ASN1.UniversalTypes.asn1_character_string
