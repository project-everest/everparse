module ASN1.DiffTest.Strings

(* Differential testing (difftest/): restricted character string types.
   Must agree with difftest/schemas/{DiffStrings,DiffStrings2,DiffVideotex}.asn *)

open ASN1.Base
open ASN1.Syntax

let utf8 = asn1_utf8string
let numeric = asn1_numericstring
let printable = asn1_printablestring
let ia5 = asn1_ia5string
let visible = asn1_visiblestring
let bmp = asn1_bMPstring
let universal = asn1_universalstring
let teletex = asn1_teletexstring
let videotex = asn1_videotexstring
let graphic = asn1_graphicstring
let general = asn1_generalstring
