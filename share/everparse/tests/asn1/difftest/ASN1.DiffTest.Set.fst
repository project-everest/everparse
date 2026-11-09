module ASN1.DiffTest.Set

(* Differential testing (difftest/): SET { ... }.
   Must agree with difftest/schemas/DiffSet.asn:

   Set ::= SET {
     a [0] IMPLICIT INTEGER,
     b [1] IMPLICIT BOOLEAN OPTIONAL,
     c OCTET STRING } *)

open ASN1.Base
open ASN1.Syntax

let ctx (x : nat {x < 31}) = mk_custom_id CONTEXT_SPECIFIC PRIMITIVE x

let set_
= asn1_set [
    "a" *^ (PLAIN ^: mk_retagged (ctx 0) asn1_integer);
    "b" *^ (OPTION ^: mk_retagged (ctx 1) asn1_boolean);
    "c" *^ (PLAIN ^: asn1_octetstring)]
    (_ by (set_tac ()))

let _ : squash (asn1_k_wf set_) = _ by (wf_tac ())
