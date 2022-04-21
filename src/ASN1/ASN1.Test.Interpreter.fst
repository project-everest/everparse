module ASN1.Test.Interpreter

open ASN1.Spec.Interpreter

let bool_id = MK_ASN1_ID UNIVERSAL PRIMITIVE 5ul

// This sample type from Antoine is not well-formed
//
// let sigAlg (seq_id:_) : asn1_k _ =
// ASN1_ILC seq_id (
// ASN1_SEQUENCE 
//   [ASN1_ILC bool_id (ASN1_TERMINAL ASN1_BOOLEAN);
//    ASN1_ILC bool_id (ASN1_TERMINAL ASN1_BOOLEAN)]
//   (admit())
// )


