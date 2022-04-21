module ASN1.Test.Interpreter

open ASN1.Spec.Interpreter

let bool_id : asn1_id_t = MK_ASN1_ID UNIVERSAL PRIMITIVE 5ul

// This sample type from Antoine is not well-formed
//
// let sigAlg (seq_id:_) : asn1_k _ =
// ASN1_ILC seq_id (
// ASN1_SEQUENCE 
//   [ASN1_ILC bool_id (ASN1_TERMINAL ASN1_BOOLEAN);
//    ASN1_ILC bool_id (ASN1_TERMINAL ASN1_BOOLEAN)]
//   (admit())
// )

let seq_id : asn1_id_t = MK_ASN1_ID UNIVERSAL CONSTRUCTED 16ul

let sigAlg : asn1_k (Set.singleton seq_id) =
  ASN1_ILC seq_id (
    ASN1_SEQUENCE 
      [ mk_ASN1_GEN_ITEM (ASN1_PLAIN_ILC (ASN1_ILC bool_id (ASN1_TERMINAL ASN1_BOOLEAN))) ;
        mk_ASN1_GEN_ITEM (ASN1_OPTION_ILC (ASN1_ILC bool_id (ASN1_TERMINAL ASN1_BOOLEAN))) ] 
       _ )
