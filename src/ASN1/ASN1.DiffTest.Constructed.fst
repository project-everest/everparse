module ASN1.DiffTest.Constructed

(* Differential testing (difftest/): SEQUENCE, SEQUENCE OF, SET OF, CHOICE
   and tagging. Must agree with difftest/schemas/DiffConstructed.asn *)

open ASN1.Base
open ASN1.Syntax

let ctx_prim (x : nat {x < pow2 32}) = mk_custom_id CONTEXT_SPECIFIC PRIMITIVE x
let ctx_cons (x : nat {x < pow2 32}) = mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED x

(* Seq ::= SEQUENCE {
     a INTEGER,
     b BOOLEAN DEFAULT FALSE,
     c [0] IMPLICIT OCTET STRING OPTIONAL,
     d [1] EXPLICIT INTEGER OPTIONAL } *)
let seq
= asn1_sequence [
    "a" *^ (PLAIN ^: asn1_integer);
    "b" *^ (DEFAULT ^: mk_default_field asn1_boolean false);
    "c" *^ (OPTION ^: mk_retagged (ctx_prim 0) asn1_octetstring);
    "d" *^ (OPTION ^: mk_prefixed (ctx_cons 1) asn1_integer)]
    (_ by (seq_tac ()))

let _ : squash (asn1_k_wf seq) = _ by (wf_tac ())

(* IntSeq ::= SEQUENCE OF INTEGER *)
let intSeq = asn1_sequence_of asn1_integer

(* OctetsSet ::= SET OF OCTET STRING *)
let octetsSet = asn1_set_of asn1_octetstring

(* Choice ::= CHOICE { i INTEGER, b BOOLEAN, o [0] IMPLICIT OCTET STRING } *)
let choice
= asn1_choice [
    "i" ^* asn1_integer;
    "b" ^* asn1_boolean;
    "o" ^* mk_retagged (ctx_prim 0) asn1_octetstring]
    (_ by (choice_tac ()))

(* App ::= [APPLICATION 5] IMPLICIT INTEGER *)
let app = mk_retagged (mk_custom_id APPLICATION PRIMITIVE 5) asn1_integer

(* PrivExp ::= [PRIVATE 3] EXPLICIT BOOLEAN *)
let privExp = mk_prefixed (mk_custom_id PRIVATE CONSTRUCTED 3) asn1_boolean

(* HighCtx ::= [100] IMPLICIT INTEGER *)
let highCtx = mk_retagged (ctx_prim 100) asn1_integer

(* HighApp ::= [APPLICATION 1000] EXPLICIT OCTET STRING *)
let highApp = mk_prefixed (mk_custom_id APPLICATION CONSTRUCTED 1000) asn1_octetstring

(* Nested ::= SEQUENCE { s Seq, l IntSeq, ch Choice OPTIONAL } *)
let nested
= asn1_sequence [
    "s" *^ (PLAIN ^: seq);
    "l" *^ (PLAIN ^: intSeq);
    "ch" *^ (OPTION ^: choice)]
    (_ by (seq_tac ()))

let _ : squash (asn1_k_wf nested) = _ by (wf_tac ())
