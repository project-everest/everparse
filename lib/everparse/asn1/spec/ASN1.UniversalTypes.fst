module ASN1.UniversalTypes

(* Schemas for the constructed universal types EXTERNAL, EMBEDDED PDV and
   CHARACTER STRING, written in terms of the existing ASN.1 combinators.
   They follow the encodings prescribed by X.690 (8.18, 8.10, 8.24) via the
   associated SEQUENCE types of X.680 (36.5, 44.5), which are defined in an
   AUTOMATIC TAGS environment: tags are IMPLICIT, except on CHOICE types,
   where they are EXPLICIT. *)

open ASN1.Base
open ASN1.Syntax

let ctx_prim (x : UInt.uint_t 32 {id_value_ok CONTEXT_SPECIFIC (FStar.UInt32.uint_to_t x)}) =
  mk_custom_id CONTEXT_SPECIFIC PRIMITIVE x

let ctx_cons (x : UInt.uint_t 32 {id_value_ok CONTEXT_SPECIFIC (FStar.UInt32.uint_to_t x)}) =
  mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED x

(* EXTERNAL (X.690 8.18.1):
   [UNIVERSAL 8] IMPLICIT SEQUENCE {
     direct-reference      OBJECT IDENTIFIER OPTIONAL,
     indirect-reference    INTEGER OPTIONAL,
     data-value-descriptor ObjectDescriptor OPTIONAL,
     encoding CHOICE {
       single-ASN1-type [0] ABSTRACT-SYNTAX.&Type,
       octet-aligned    [1] IMPLICIT OCTET STRING,
       arbitrary        [2] IMPLICIT BIT STRING } } *)

let external_encoding
= asn1_choice [
    "single-ASN1-type" ^* (mk_prefixed (ctx_cons 0) asn1_any);
    "octet-aligned" ^* (mk_retagged (ctx_prim 1) asn1_octetstring);
    "arbitrary" ^* (mk_retagged (ctx_prim 2) asn1_bitstring)]
    (_ by (choice_tac ()))

let external_id = mk_constant_constructed_id 8

let asn1_external
= mk_retagged external_id
  (asn1_sequence [
    "direct-reference" *^ (OPTION ^: asn1_oid);
    "indirect-reference" *^ (OPTION ^: asn1_integer);
    "data-value-descriptor" *^ (OPTION ^: asn1_objectdescriptor);
    "encoding" *^ (PLAIN ^: external_encoding)]
    (_ by (seq_tac ())))

(* The `identification` CHOICE shared by EMBEDDED PDV and CHARACTER STRING
   (X.680 36.5, 44.5). *)

let identification_syntaxes
= asn1_sequence [
    "abstract" *^ (PLAIN ^: mk_retagged (ctx_prim 0) asn1_oid);
    "transfer" *^ (PLAIN ^: mk_retagged (ctx_prim 1) asn1_oid)]
    (_ by (seq_tac ()))

let identification_context_negotiation
= asn1_sequence [
    "presentation-context-id" *^ (PLAIN ^: mk_retagged (ctx_prim 0) asn1_integer);
    "transfer-syntax" *^ (PLAIN ^: mk_retagged (ctx_prim 1) asn1_oid)]
    (_ by (seq_tac ()))

let identification
= asn1_choice [
    "syntaxes" ^* (mk_retagged (ctx_cons 0) identification_syntaxes);
    "syntax" ^* (mk_retagged (ctx_prim 1) asn1_oid);
    "presentation-context-id" ^* (mk_retagged (ctx_prim 2) asn1_integer);
    "context-negotiation" ^* (mk_retagged (ctx_cons 3) identification_context_negotiation);
    "transfer-syntax" ^* (mk_retagged (ctx_prim 4) asn1_oid);
    "fixed" ^* (mk_retagged (ctx_prim 5) asn1_null)]
    (_ by (choice_tac ()))

(* EMBEDDED PDV (X.690 8.10, X.680 36.5):
   [UNIVERSAL 11] IMPLICIT SEQUENCE {
     identification [0] EXPLICIT CHOICE { ... },
     data-value     [2] IMPLICIT OCTET STRING }
   (data-value-descriptor [1] is ABSENT by the WITH COMPONENTS constraint) *)

let embedded_pdv_id = mk_constant_constructed_id 11

let asn1_embedded_pdv
= mk_retagged embedded_pdv_id
  (asn1_sequence [
    "identification" *^ (PLAIN ^: mk_prefixed (ctx_cons 0) identification);
    "data-value" *^ (PLAIN ^: mk_retagged (ctx_prim 2) asn1_octetstring)]
    (_ by (seq_tac ())))

(* CHARACTER STRING (X.690 8.24, X.680 44.5):
   [UNIVERSAL 29] IMPLICIT SEQUENCE {
     identification [0] EXPLICIT CHOICE { ... },
     string-value   [2] IMPLICIT OCTET STRING } *)

let character_string_id = mk_constant_constructed_id 29

let asn1_character_string
= mk_retagged character_string_id
  (asn1_sequence [
    "identification" *^ (PLAIN ^: mk_prefixed (ctx_cons 0) identification);
    "string-value" *^ (PLAIN ^: mk_retagged (ctx_prim 2) asn1_octetstring)]
    (_ by (seq_tac ())))
