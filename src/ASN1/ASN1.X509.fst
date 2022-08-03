module ASN1.X509

module U32 = FStar.UInt32
module List = FStar.List.Tot

open ASN1.Base

(* Known looseness from rfc5280 section-4:
   . Not enforcing version = 0, 1, or 2
   . Not enforcing issuerUniqueID, subjectUniqueID, and extensions only appear with certain version numbers
   . Not enforcing the algorithmIdentifier in the signature, subjectPublicKeyInfo, and signatureAlgorithm being consistent (it is more complicated than simple equivalence in some cases)
   . Not parsing extension value field of extensions
   . Not backward-compact in name
   . Only support algorithms included in the list
*)

//shorthands

let mk_constant_id (x : U32.t) : asn1_id_t
= MK_ASN1_ID UNIVERSAL PRIMITIVE x

let mk_custom_id (x : U32.t) : asn1_id_t
= MK_ASN1_ID CONTEXT_SPECIFIC PRIMITIVE x

// for sequences

let field_type (s : Set.set asn1_id_t) (d : asn1_decorator) 
= match d with
  | DEFAULT -> asn1_decorated_k s d
  | _ -> asn1_k s

let op_Hat_Colon (#s : Set.set asn1_id_t)  
  (d : asn1_decorator) 
  (f : field_type s d)
: asn1_gen_item_k
= match d with
  | DEFAULT -> mk_ASN1_GEN_ITEM #s #d f
  | PLAIN -> mk_ASN1_GEN_ITEM (ASN1_PLAIN_ILC #s f)
  | OPTION -> mk_ASN1_GEN_ITEM (ASN1_OPTION_ILC #s f)

// constants

let boolean_id = mk_constant_id 1ul

let integer_id = mk_constant_id 2ul

let bit_string_id = mk_constant_id 3ul

let octet_string_id = mk_constant_id 4ul

let null_id = mk_constant_id 5ul

let oid_id = mk_constant_id 6ul

let utf8string_id = mk_constant_id 12ul

let sequence_id = mk_constant_id 16ul

let set_id = mk_constant_id 17ul

let printablestring_id = mk_constant_id 19ul

// let ia5string_id = mk_constant_id 22ul

let utctime_id = mk_constant_id 23ul

let generalizedtime_id = mk_constant_id 24ul

// TODO: insert list of supported algorithms here

(*
let md2_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 2ul; 2ul]

let md5_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 2ul; 5ul]

let id_sha1_oid : asn1_oid_t = [1ul; 3ul; 14ul; 3ul; 2ul; 26ul]
*)

let md2WithRSAEncryption_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 1ul; 1ul; 2ul]

let md5WithRSAEncryption_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 1ul; 1ul; 4ul]

let sha_1WithRSAEncryption_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 1ul; 1ul; 5ul]

let default_NULL_field
= mk_ASN1_GEN_ITEM (ASN1_DEFAULT_TERMINAL null_id #(ASN1_NULL) ())

let supported_algorithms
= [(md2WithRSAEncryption_oid, default_NULL_field);
   (md5WithRSAEncryption_oid, default_NULL_field);
   (sha_1WithRSAEncryption_oid, default_NULL_field)]

let supported_algorithms_wf : squash (List.noRepeats (List.map fst supported_algorithms))
= _

let version_id = mk_custom_id 0ul

//Warning: no restriction on the version value

let version_field : asn1_decorated_k _ _
= ASN1_DEFAULT_TERMINAL version_id #(ASN1_PREFIXED_TERMINAL integer_id ASN1_INTEGER) 0l

let serialNumber_ilc
= ASN1_ILC integer_id (ASN1_TERMINAL ASN1_INTEGER)

let algorithmIdentifier_ilc
= ASN1_ILC sequence_id
    (ASN1_ANY_OID supported_algorithms supported_algorithms_wf)

let signature_ilc = algorithmIdentifier_ilc

let attributeType_ilc
= ASN1_ILC oid_id (ASN1_TERMINAL ASN1_OID)

//Warning: backward compatibility, dependency on attributetype 

let directoryString_ilc
= ASN1_CHOICE_ILC 
  [(printablestring_id, ASN1_TERMINAL ASN1_PRINTABLESTRING);
   (utf8string_id, ASN1_TERMINAL ASN1_UTF8STRING)]
  _

let attributeValue_ilc = directoryString_ilc

let attributeTypeAndValue_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE [
      PLAIN ^: attributeType_ilc;
      PLAIN ^: attributeValue_ilc] _)

let relativeDistinguishedName_ilc
= ASN1_ILC set_id
    (ASN1_SET_OF attributeTypeAndValue_ilc)

let rDNSequence_c
= ASN1_SEQUENCE_OF relativeDistinguishedName_ilc

let name_ilc
= ASN1_CHOICE_ILC [(sequence_id, rDNSequence_c)] _

let issuer_ilc = name_ilc

let asn1_time_k : asn1_k _
= ASN1_CHOICE_ILC 
  [(utctime_id, (ASN1_TERMINAL ASN1_UTCTIME)); 
   (generalizedtime_id, (ASN1_TERMINAL ASN1_GENERALIZEDTIME))]
  _
  
let notBefore = asn1_time_k

let notAfter = asn1_time_k

let validity_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE [
      PLAIN ^: notBefore;
      PLAIN ^: notAfter] _)

let subject_ilc = name_ilc

let algorithm_ilc = algorithmIdentifier_ilc

let subjectPublicKey_ilc
= ASN1_ILC bit_string_id (ASN1_TERMINAL ASN1_BITSTRING)

let subjectPublicKeyInfo_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE [
      PLAIN ^: algorithm_ilc;
      PLAIN ^: subjectPublicKey_ilc] _)

let uniqueIdentifier_c
= (ASN1_TERMINAL ASN1_BITSTRING)

let issuerUniqueId_id = mk_custom_id 1ul

//Warning: no restriction from the version number

let issuerUniqueId_ilc
= ASN1_ILC issuerUniqueId_id uniqueIdentifier_c

let subjectUniqueId_id = mk_custom_id 2ul


//Warning: no restriction from the version number

let subjectUniqueId_ilc
= ASN1_ILC subjectUniqueId_id uniqueIdentifier_c

let extnID_ilc
= ASN1_ILC oid_id (ASN1_TERMINAL ASN1_OID)

let critical_field
= ASN1_DEFAULT_TERMINAL boolean_id #(ASN1_BOOLEAN) false

//Warning: weak type, should be dependent on extnID
let extnValue_ilc
= ASN1_ILC octet_string_id (ASN1_TERMINAL ASN1_OCTETSTRING)

let extension_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE [
     PLAIN ^: extnID_ilc;
     DEFAULT ^: critical_field;
     PLAIN ^: extnValue_ilc] _)

let extensions_id = mk_custom_id 3ul

//Warning: no restriction from the version number

let extensions_ilc' 
= ASN1_ILC sequence_id (ASN1_SEQUENCE_OF extension_ilc)

let extensions_ilc
= ASN1_ILC extensions_id (ASN1_PREFIXED extensions_ilc')

//Need to unroll the recursive definition of the sequence_wf
#push-options "--max_fuel 16"

let x509_TBSCertificate_ilc
= ASN1_ILC sequence_id 
    (ASN1_SEQUENCE [
      DEFAULT ^: version_field;
      PLAIN ^: serialNumber_ilc;
      PLAIN ^: signature_ilc;
      PLAIN ^: issuer_ilc;
      PLAIN ^: validity_ilc;
      PLAIN ^: subject_ilc;
      PLAIN ^: subjectPublicKeyInfo_ilc;
      OPTION ^: issuerUniqueId_ilc;
      OPTION ^: subjectUniqueId_ilc;
      OPTION ^: extensions_ilc] _)
    
#pop-options

let signatureAlgorithm_ilc = algorithmIdentifier_ilc

let signatureValue_ilc
= ASN1_ILC bit_string_id (ASN1_TERMINAL ASN1_BITSTRING)

let x509_certificate_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE [
      PLAIN ^: x509_TBSCertificate_ilc;
      PLAIN ^: signatureAlgorithm_ilc;
      PLAIN ^: signatureValue_ilc] _)

// let's go boom!

open ASN1.Spec.Interpreter

let x509_certificate_parser = asn1_as_parser x509_certificate_ilc
