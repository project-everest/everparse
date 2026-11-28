module ASN1.DiffTest.Smoke

(* Differential testing (difftest/), walking-skeleton schema.
   Must agree with difftest/schemas/DiffSmoke.asn:

   Smoke ::= SEQUENCE {
     a INTEGER,
     b BOOLEAN OPTIONAL,
     c OCTET STRING }
*)

open ASN1.Base
open ASN1.Syntax

let smoke
= asn1_sequence [
    "a" *^ (PLAIN ^: asn1_integer);
    "b" *^ (OPTION ^: asn1_boolean);
    "c" *^ (PLAIN ^: asn1_octetstring)]
    (_ by (seq_tac ()))

let _ : squash (asn1_k_wf smoke) = _ by (wf_tac ())
