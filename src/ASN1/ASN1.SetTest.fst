module ASN1.SetTest

(* A test schema exercising SET { ... } (X.690 10.3: components in
   canonical tag order, OPTIONAL and DEFAULT components, a CHOICE
   component tagged by its alternative) *)

open ASN1.Base
open ASN1.Syntax

let ctx (x : nat {x < 31}) = mk_custom_id CONTEXT_SPECIFIC PRIMITIVE x

(* SetTest ::= SET {
     a [0] IMPLICIT INTEGER,
     b [1] IMPLICIT INTEGER OPTIONAL,
     c CHOICE { c2 [2] IMPLICIT BOOLEAN, c5 [5] IMPLICIT NULL },
     d [3] IMPLICIT BOOLEAN DEFAULT TRUE,
     e OCTET STRING OPTIONAL }
*)
let setTest
= asn1_set [
    "a" *^ (PLAIN ^: mk_retagged (ctx 0) asn1_integer);
    "b" *^ (OPTION ^: mk_retagged (ctx 1) asn1_integer);
    "c" *^ (PLAIN ^: asn1_choice [
                       "c2" ^* mk_retagged (ctx 2) asn1_boolean;
                       "c5" ^* mk_retagged (ctx 5) asn1_null]
                       (_ by (choice_tac ())));
    "d" *^ (DEFAULT ^: mk_default_field (mk_retagged (ctx 3) asn1_boolean) true);
    "e" *^ (OPTION ^: asn1_octetstring)]
    (_ by (set_tac ()))

let _ : squash (asn1_k_wf setTest) = _ by (wf_tac ())

open ASN1.Spec.Interpreter

let settest_parser = asn1_as_parser setTest

let parse_settest (b:bytes) = settest_parser b

let dparse_settest (b:bytes) = dasn1_as_parser setTest b
