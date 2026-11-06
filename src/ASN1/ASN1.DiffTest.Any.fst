module ASN1.DiffTest.Any

(* Differential testing (difftest/): ANY and ANY DEFINED BY.
   Must agree with difftest/schemas/DiffAny.asn:

   AnyT ::= ANY
   AlgId ::= SEQUENCE {
     algorithm OBJECT IDENTIFIER,
     parameters ANY DEFINED BY algorithm OPTIONAL }

   where the parameters of algorithm 1.2.3 must be NULL, as expressed
   there by the everparse-asn1 directive
   --#DEFINED-BY AlgId.parameters { alg-123 : NULL } *)

open ASN1.Base
open ASN1.Syntax

let anyT = asn1_any

let alg_123 = mk_oid [1; 2; 3]

let alg_123_parameters
= mk_gen_items ["parameters" *^ (PLAIN ^: asn1_null)] (_ by (seq_tac ()))

let fallback_parameters
= mk_gen_items ["parameters" *^ (OPTION ^: asn1_any)] (_ by (seq_tac ()))

let algId
= asn1_any_oid_with_fallback
    "algorithm"
    [(alg_123, alg_123_parameters)]
    fallback_parameters
    (_ by (seq_tac ()))
    (_ by (choice_tac ()))
