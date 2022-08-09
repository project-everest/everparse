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

let reduce = ()

//shorthands

[@@reduce]
let mk_constant_id (x : U32.t) : asn1_id_t
= MK_ASN1_ID UNIVERSAL PRIMITIVE x

[@@reduce]
let mk_custom_id (x : U32.t) : asn1_id_t
= MK_ASN1_ID CONTEXT_SPECIFIC PRIMITIVE x

// for sequences

[@@reduce]
let field_type (s : Set.set asn1_id_t) (d : asn1_decorator) 
= match d with
  | DEFAULT -> asn1_decorated_k s d
  | _ -> asn1_k s

[@@reduce]
let op_Hat_Colon (#s : Set.set asn1_id_t)  
  (d : asn1_decorator) 
  (f : field_type s d)
: asn1_gen_item_k
= match d with
  | DEFAULT -> mk_ASN1_GEN_ITEM #s #d f
  | PLAIN -> mk_ASN1_GEN_ITEM (ASN1_PLAIN_ILC #s f)
  | OPTION -> mk_ASN1_GEN_ITEM (ASN1_OPTION_ILC #s f)

// constants

[@@reduce]
let boolean_id = mk_constant_id 1ul

[@@reduce]
let integer_id = mk_constant_id 2ul

[@@reduce]
let bit_string_id = mk_constant_id 3ul

[@@reduce]
let octet_string_id = mk_constant_id 4ul

[@@reduce]
let null_id = mk_constant_id 5ul

[@@reduce]
let oid_id = mk_constant_id 6ul

[@@reduce]
let utf8string_id = mk_constant_id 12ul

[@@reduce]
let sequence_id = mk_constant_id 16ul

[@@reduce]
let set_id = mk_constant_id 17ul

[@@reduce]
let printablestring_id = mk_constant_id 19ul

// let ia5string_id = mk_constant_id 22ul

[@@reduce]
let utctime_id = mk_constant_id 23ul

[@@reduce]
let generalizedtime_id = mk_constant_id 24ul

// TODO: insert list of supported algorithms here

(*
let md2_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 2ul; 2ul]

let md5_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 2ul; 5ul]

let id_sha1_oid : asn1_oid_t = [1ul; 3ul; 14ul; 3ul; 2ul; 26ul]
*)

[@@reduce]
let md2WithRSAEncryption_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 1ul; 1ul; 2ul]

[@@reduce]
let md5WithRSAEncryption_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 1ul; 1ul; 4ul]

[@@reduce]
let sha_1WithRSAEncryption_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 1ul; 1ul; 5ul]

[@@reduce]
let default_NULL_field
= (ASN1_DEFAULT_TERMINAL null_id #(ASN1_NULL) ())

[@@reduce]
let default_NULL_field_list
= [DEFAULT ^: default_NULL_field]

[@@reduce]
let default_NULL_field_list_with_pf : asn1_gen_items_k
= (|default_NULL_field_list, _|)

[@@reduce]
let supported_algorithms
= [(md2WithRSAEncryption_oid, default_NULL_field_list_with_pf);
   (md5WithRSAEncryption_oid, default_NULL_field_list_with_pf);
   (sha_1WithRSAEncryption_oid, default_NULL_field_list_with_pf)]

let supported_algorithms_wf : squash (List.noRepeats (List.map fst supported_algorithms))
= _

[@@reduce]
let fallback_sequence_bitstring
= ASN1_ILC sequence_id (ASN1_TERMINAL ASN1_BITSTRING)

[@@reduce]
let fallback_sequence_bitstring_field_list_with_pf : asn1_gen_items_k
= (| [OPTION ^: fallback_sequence_bitstring], _ |)

[@@reduce]
let version_id = mk_custom_id 0ul

//Warning: no restriction on the version value

[@@reduce]
let version_field : asn1_decorated_k _ _
= ASN1_DEFAULT_TERMINAL version_id #(ASN1_PREFIXED_TERMINAL integer_id ASN1_INTEGER) 0l

[@@reduce]
let serialNumber_ilc
= ASN1_ILC integer_id (ASN1_TERMINAL ASN1_INTEGER)

[@@reduce]
let algorithmIdentifier_ilc
= ASN1_ILC sequence_id
    (ASN1_ANY_OID oid_id supported_algorithms (Some fallback_sequence_bitstring_field_list_with_pf) supported_algorithms_wf)

[@@reduce]
let signature_ilc = algorithmIdentifier_ilc

[@@reduce]
let attributeType_ilc
= ASN1_ILC oid_id (ASN1_TERMINAL ASN1_OID)

//Warning: backward compatibility, dependency on attributetype 

[@@reduce]
let directoryString_ilc
= ASN1_CHOICE_ILC 
  [(printablestring_id, ASN1_TERMINAL ASN1_PRINTABLESTRING);
   (utf8string_id, ASN1_TERMINAL ASN1_UTF8STRING)]
  _

[@@reduce]
let attributeValue_ilc = directoryString_ilc

[@@reduce]
let attributeTypeAndValue_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE (| [
      PLAIN ^: attributeType_ilc;
      PLAIN ^: attributeValue_ilc], _|))

[@@reduce]
let relativeDistinguishedName_ilc
= ASN1_ILC set_id
    (ASN1_SET_OF attributeTypeAndValue_ilc)

[@@reduce]
let rDNSequence_c
= ASN1_SEQUENCE_OF relativeDistinguishedName_ilc

[@@reduce]
let name_ilc
= ASN1_CHOICE_ILC [(sequence_id, rDNSequence_c)] _

[@@reduce]
let issuer_ilc = name_ilc

[@@reduce]
let asn1_time_k : asn1_k _
= ASN1_CHOICE_ILC 
  [(utctime_id, (ASN1_TERMINAL ASN1_UTCTIME)); 
   (generalizedtime_id, (ASN1_TERMINAL ASN1_GENERALIZEDTIME))]
  _
  
[@@reduce]
let notBefore = asn1_time_k

[@@reduce]
let notAfter = asn1_time_k

[@@reduce]
let validity_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE (|[
      PLAIN ^: notBefore;
      PLAIN ^: notAfter], _|))

[@@reduce]
let subject_ilc = name_ilc

[@@reduce]
let algorithm_ilc = algorithmIdentifier_ilc

[@@reduce]
let subjectPublicKey_ilc
= ASN1_ILC bit_string_id (ASN1_TERMINAL ASN1_BITSTRING)

[@@reduce]
let subjectPublicKeyInfo_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE (|[
      PLAIN ^: algorithm_ilc;
      PLAIN ^: subjectPublicKey_ilc], _|))

[@@reduce]
let uniqueIdentifier_c
= (ASN1_TERMINAL ASN1_BITSTRING)

[@@reduce]
let issuerUniqueId_id = mk_custom_id 1ul

//Warning: no restriction from the version number

[@@reduce]
let issuerUniqueId_ilc
= ASN1_ILC issuerUniqueId_id uniqueIdentifier_c

[@@reduce]
let subjectUniqueId_id = mk_custom_id 2ul


//Warning: no restriction from the version number

[@@reduce]
let subjectUniqueId_ilc
= ASN1_ILC subjectUniqueId_id uniqueIdentifier_c

[@@reduce]
let extnID_ilc
= ASN1_ILC oid_id (ASN1_TERMINAL ASN1_OID)

[@@reduce]
let critical_field
= ASN1_DEFAULT_TERMINAL boolean_id #(ASN1_BOOLEAN) false

//Warning: weak type, should be dependent on extnID
[@@reduce]
let extnValue_ilc
= ASN1_ILC octet_string_id (ASN1_TERMINAL ASN1_OCTETSTRING)

[@@reduce]
let extension_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE (|[
     PLAIN ^: extnID_ilc;
     DEFAULT ^: critical_field;
     PLAIN ^: extnValue_ilc], _|))

[@@reduce]
let extensions_id = mk_custom_id 3ul

//Warning: no restriction from the version number

[@@reduce]
let extensions_ilc' 
= ASN1_ILC sequence_id (ASN1_SEQUENCE_OF extension_ilc)

[@@reduce]
let extensions_ilc
= ASN1_ILC extensions_id (ASN1_PREFIXED extensions_ilc')

//Need to unroll the recursive definition of the sequence_wf
#push-options "--max_fuel 16"

[@@reduce]
let x509_TBSCertificate_ilc
= ASN1_ILC sequence_id 
    (ASN1_SEQUENCE (|[
      DEFAULT ^: version_field;
      PLAIN ^: serialNumber_ilc;
      PLAIN ^: signature_ilc;
      PLAIN ^: issuer_ilc;
      PLAIN ^: validity_ilc;
      PLAIN ^: subject_ilc;
      PLAIN ^: subjectPublicKeyInfo_ilc;
      OPTION ^: issuerUniqueId_ilc;
      OPTION ^: subjectUniqueId_ilc;
      OPTION ^: extensions_ilc], _|))
    
#pop-options

[@@reduce]
let signatureAlgorithm_ilc = algorithmIdentifier_ilc

[@@reduce]
let signatureValue_ilc
= ASN1_ILC bit_string_id (ASN1_TERMINAL ASN1_BITSTRING)

[@@reduce]
let x509_certificate_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE (|[
      PLAIN ^: x509_TBSCertificate_ilc;
      PLAIN ^: signatureAlgorithm_ilc;
      PLAIN ^: signatureValue_ilc], _|))

///
//let's go boom!

open ASN1.Spec.Interpreter

module T = FStar.Tactics

// let x509_tbs_certificate_parser = asn1_as_parser attributeTypeAndValue_ilc fallback_sequence_bitstring signatureAlgorithm_ilc

// [@@T.postprocess_with (fun _ -> T.norm [delta;
//                                      zeta;
//                                      iota;
//                                      primops];
//                              T.trefl())]
let x509_certificate_parser = asn1_as_parser x509_certificate_ilc

[@@normalize_for_extraction [delta;
                             zeta;
                             iota;
                             primops]]
let parse_cert (b:bytes) = x509_certificate_parser b
