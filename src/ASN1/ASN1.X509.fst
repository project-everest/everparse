module ASN1.X509

module U32 = FStar.UInt32
module List = FStar.List.Tot

open ASN1.Base

(* Known looseness from rfc5280 section-4:
   . Enforcing version must be 2 (v3)
   . Enforcing extensions must appear
   . Enforced by crypto: the algorithmIdentifier in the signature, subjectPublicKeyInfo, and signatureAlgorithm being consistent
   . Not parsing extension value field of extensions
   . TODO: A list of constants for Name
   . Backward compatibility for Name
   . Only support algorithms and extensions included in the list
*)

//shorthands

let mk_constant_id (x : UInt.uint_t 32) : asn1_id_t
= MK_ASN1_ID UNIVERSAL PRIMITIVE (U32.uint_to_t x)

let mk_constant_constructed_id (x : UInt.uint_t 32) : asn1_id_t
= MK_ASN1_ID UNIVERSAL CONSTRUCTED (U32.uint_to_t x)

let mk_custom_id (c : asn1_id_class_t) (f : asn1_id_flag_t) (x : UInt.uint_t 32) : asn1_id_t
= MK_ASN1_ID c f (U32.uint_to_t x)

let rec mk_u32list (l : list (UInt.uint_t 32)) : list U32.t
= match l with
  | [] -> []
  | hd :: tl -> (U32.uint_to_t hd) :: (mk_u32list tl)

let mk_oid (l : list (UInt.uint_t 32)) : Pure (asn1_oid_t)
  (requires asn1_OID_wf (mk_u32list l))
  (ensures fun _ -> True)
= mk_u32list l

let mk_oid_app (oid : asn1_oid_t) (x : UInt.uint_t 32) : asn1_oid_t
= List.append oid [U32.uint_to_t x]

let op_Slash_Plus = mk_oid_app

// for choices

let op_Hat_Star (id : asn1_id_t) (name : string) : asn1_content_k -> (asn1_id_t * asn1_content_k)
= fun f -> (id, f)

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

let boolean_id = mk_constant_id 1

let integer_id = mk_constant_id 2

let bit_string_id = mk_constant_id 3

let octet_string_id = mk_constant_id 4

let null_id = mk_constant_id 5

let oid_id = mk_constant_id 6

let utf8string_id = mk_constant_id 12

let sequence_id = mk_constant_constructed_id 16

let set_id = mk_constant_constructed_id 17

let printablestring_id = mk_constant_id 19

let ia5string_id = mk_constant_id 22

let utctime_id = mk_constant_id 23

let generalizedtime_id = mk_constant_id 24

// TODO: insert list of supported algorithms here

(*
let md2_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 2ul; 2ul]

let md5_oid : asn1_oid_t = [1ul; 2ul; 840ul; 113549ul; 2ul; 5ul]

let id_sha1_oid : asn1_oid_t = [1ul; 3ul; 14ul; 3ul; 2ul; 26ul]
*)

let rSAEncryption_oid = mk_oid [1;2;840;113549;1;1;1]

let md2WithRSAEncryption_oid = mk_oid [1;2;840;113549;1;1;2]

let md5WithRSAEncryption_oid = mk_oid [1;2;840;113549;1;1;4]

let sha_1WithRSAEncryption_oid = mk_oid [1;2;840;113549;1;1;5]

let sha256WithRSAEncryption_oid = mk_oid [1;2;840;113549;1;1;11]

let option_NULL_field
= ASN1_ILC null_id (ASN1_TERMINAL ASN1_NULL)

let option_NULL_field_list
= [OPTION ^: option_NULL_field]

let option_NULL_field_list_with_pf : asn1_gen_items_k
= (|option_NULL_field_list, _|)

let supported_algorithms
= [(rSAEncryption_oid, option_NULL_field_list_with_pf);
   (md2WithRSAEncryption_oid, option_NULL_field_list_with_pf);
   (md5WithRSAEncryption_oid, option_NULL_field_list_with_pf);
   (sha_1WithRSAEncryption_oid, option_NULL_field_list_with_pf);
   (sha256WithRSAEncryption_oid, option_NULL_field_list_with_pf)]

let fallback_sequence_bitstring
= ASN1_ILC sequence_id (ASN1_TERMINAL ASN1_OCTETSTRING)

let fallback_sequence_bitstring_field_list_with_pf : asn1_gen_items_k
= (| [OPTION ^: fallback_sequence_bitstring], _ |)

let version_id = mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0

let version_field : asn1_k _
= ASN1_ILC version_id (ASN1_RESTRICTED_TERMINAL (ASN1_PREFIXED_TERMINAL integer_id ASN1_INTEGER) (fun x -> x = 2))

let serialNumber_ilc
= ASN1_ILC integer_id (ASN1_TERMINAL ASN1_INTEGER)

let algorithmIdentifier_ilc
= ASN1_ILC sequence_id
    (ASN1_ANY_OID oid_id supported_algorithms (Some fallback_sequence_bitstring_field_list_with_pf) 
    (assert (List.noRepeats (List.map fst supported_algorithms)) by (Tactics.trivial ())))

let signature_ilc = algorithmIdentifier_ilc

let attributeType_ilc
= ASN1_ILC oid_id (ASN1_TERMINAL ASN1_OID)

//Warning: backward compatibility

//Warning: a list of constants might be needed here

let directoryString_ilc
= ASN1_CHOICE_ILC 
  [(printablestring_id, ASN1_TERMINAL ASN1_PRINTABLESTRING);
   (utf8string_id, ASN1_TERMINAL ASN1_UTF8STRING)]
  _

let attributeValue_ilc = directoryString_ilc

let attributeTypeAndValue_ilc
= ASN1_ILC sequence_id
    (ASN1_ANY_OID oid_id [] (Some (|[PLAIN ^: attributeValue_ilc], _|)) _)

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
    (ASN1_SEQUENCE (|[
      PLAIN ^: notBefore;
      PLAIN ^: notAfter], _|))

let subject_ilc = name_ilc

let algorithm_ilc = algorithmIdentifier_ilc

let subjectPublicKey_ilc
= ASN1_ILC bit_string_id (ASN1_TERMINAL ASN1_BITSTRING)

let subjectPublicKeyInfo_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE (|[
      PLAIN ^: algorithm_ilc;
      PLAIN ^: subjectPublicKey_ilc], _|))

let uniqueIdentifier_c
= (ASN1_TERMINAL ASN1_BITSTRING)

let issuerUniqueId_id = mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1

let issuerUniqueId_ilc
= ASN1_ILC issuerUniqueId_id uniqueIdentifier_c

let subjectUniqueId_id = mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 2

let subjectUniqueId_ilc
= ASN1_ILC subjectUniqueId_id uniqueIdentifier_c

let id_pkix = mk_oid [1;3;6;1;5;5;7]

let id_pe = id_pkix /+ 1

let id_pe_authorityInformationAccess = id_pe /+ 1

//Warning: Using the mitls spec which is loosened from rfc5280

let mk_expansion (critical : asn1_gen_item_k) (#s : _) (value : asn1_k s) : Pure asn1_gen_items_k
  (requires (asn1_sequence_k_wf ([(fun x -> match x with |(| s, d, _ |) -> (s, d)) critical; (Set.singleton octet_string_id, PLAIN)])))
  (ensures fun _ -> True)
= let f = fun (x : asn1_gen_item_k) -> match x with | (|s, d, _|) -> (s, d) in
  let items = [critical; PLAIN ^: (ASN1_ILC octet_string_id (ASN1_PREFIXED value))] in
  assert (List.map f items == [f critical; (Set.singleton octet_string_id, PLAIN)]);
  (| items, _ |)

let id_ad = id_pkix /+ 48

let id_ad_caIssuers = id_ad /+ 1

let id_ad_ocsp = id_ad /+ 2

let accessMethod_ilc
= ASN1_ILC oid_id (ASN1_RESTRICTED_TERMINAL ASN1_OID (fun oid -> oid = id_ad_caIssuers && oid = id_ad_ocsp))

let generalName_ilc
= ASN1_CHOICE_ILC 
  [(((mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1) ^* "email") (ASN1_TERMINAL ASN1_IA5STRING));
   (((mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 2) ^* "dns") (ASN1_TERMINAL ASN1_IA5STRING));
   (((mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 4) ^* "x500") rDNSequence_c);
   (((mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 6) ^* "uri") (ASN1_TERMINAL ASN1_IA5STRING));
   (((mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 7) ^* "ip") (ASN1_TERMINAL ASN1_IA5STRING));
   (((mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 8) ^* "registeredID") (ASN1_TERMINAL ASN1_OID))]
  _

let generalNames_ilc = ASN1_ILC sequence_id (ASN1_SEQUENCE_OF generalName_ilc)

let generalNames_c = ASN1_SEQUENCE_OF generalName_ilc

let accessLocation_ilc
= generalName_ilc

let accessDescription_ilc
= ASN1_ILC sequence_id 
   (ASN1_SEQUENCE (|[
     PLAIN ^: accessMethod_ilc;
     PLAIN ^: accessLocation_ilc], _|))

let authorityInfoAccessSyntax_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE_OF accessDescription_ilc)

let critical_field
= ASN1_DEFAULT_TERMINAL boolean_id #(ASN1_BOOLEAN) false

let critical_field_MUST_false
= ASN1_DEFAULT_RESTRICTED_TERMINAL boolean_id #(ASN1_BOOLEAN) (fun b -> b = false) false

let critical_field_MUST_true
= ASN1_ILC boolean_id (ASN1_RESTRICTED_TERMINAL ASN1_BOOLEAN (fun b -> b))

let authorityInformationAcess_expansion
= mk_expansion (DEFAULT ^: critical_field_MUST_false) authorityInfoAccessSyntax_ilc

let id_ce = mk_oid [2;5;29]

let id_ce_subjectKeyIdentifier = id_ce /+ 14

let subjectKeyIdentifier_ilc = ASN1_ILC octet_string_id (ASN1_TERMINAL ASN1_OCTETSTRING)

let subjectKeyIdentifier_expansion 
= mk_expansion (DEFAULT ^: critical_field_MUST_false) subjectKeyIdentifier_ilc

let id_ce_keyUsage = id_ce /+ 15

let keyUsage_ilc = ASN1_ILC bit_string_id (ASN1_TERMINAL ASN1_BITSTRING)

let keyUsage_expansion
= mk_expansion (DEFAULT ^: critical_field) keyUsage_ilc

let id_ce_subjectAlternativeName = id_ce /+ 17

let subjectAlternativeName_expansion 
= mk_expansion (DEFAULT ^: critical_field) generalNames_ilc

let id_ce_basicConstraints = id_ce /+ 19

let basicConstraints_cA_field = ASN1_DEFAULT_TERMINAL boolean_id #(ASN1_BOOLEAN) false

let pathLenConstraint = ASN1_ILC integer_id (ASN1_RESTRICTED_TERMINAL ASN1_INTEGER (fun x -> x >= 0))

let basicConstraints_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE (|[
     DEFAULT ^: basicConstraints_cA_field;
     OPTION ^: pathLenConstraint], _ |))

let basicConstraints_expansion
= mk_expansion (DEFAULT ^: critical_field) basicConstraints_ilc

let id_ce_cRLDistributionPoints = id_ce /+ 31

let distributionPointName_ilc
= ASN1_CHOICE_ILC [
    (((mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) ^* "fullName") (generalNames_c));
    (((mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 1) ^* "nameRelativeToCRLIssuer") (rDNSequence_c))] _

let reasonFlags_ilc
= ASN1_ILC bit_string_id (ASN1_TERMINAL ASN1_BITSTRING)

let distributionPoint_ilc
= ASN1_ILC sequence_id 
    (ASN1_SEQUENCE (|[
     OPTION ^: (ASN1_ILC (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) (ASN1_PREFIXED distributionPointName_ilc));
     OPTION ^: (ASN1_ILC (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 1) (ASN1_PREFIXED reasonFlags_ilc));
     OPTION ^: (ASN1_ILC (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 2) (ASN1_PREFIXED generalNames_ilc))], _ |))

let cRLDistributionPoints
= ASN1_ILC sequence_id (ASN1_SEQUENCE_OF distributionPoint_ilc)

let cRLDistributionPoints_expansion
= mk_expansion (DEFAULT ^: critical_field) cRLDistributionPoints

let id_ce_certificatePolicies = id_ce /+ 32

let cPSuri_c = ASN1_TERMINAL ASN1_IA5STRING

let qualifier_ilc = ASN1_CHOICE_ILC [(ia5string_id, cPSuri_c)] _

let qualifier_fields_with_pf : asn1_gen_items_k
= (| [PLAIN ^: qualifier_ilc], _ |)

let id_qt = id_pkix /+ 2

let id_qt_cps = id_qt /+ 1

let supported_policyQualifier
= [(id_qt_cps, qualifier_fields_with_pf)]

let supported_policyQualifier_wf : squash (List.noRepeats (List.map fst supported_policyQualifier)) = _

let policyQualifierInfo_ilc
= ASN1_ILC sequence_id (ASN1_ANY_OID oid_id supported_policyQualifier None supported_policyQualifier_wf)

let policyIdentifier_ilc = ASN1_ILC oid_id (ASN1_TERMINAL ASN1_OID)

let policyInformation_ilc
= ASN1_ILC sequence_id 
    (ASN1_SEQUENCE (|[
     PLAIN ^: policyIdentifier_ilc;
     OPTION ^: (ASN1_ILC sequence_id (ASN1_SEQUENCE_OF policyQualifierInfo_ilc))], _|))

let certificatePolicies_ilc
= ASN1_ILC sequence_id (ASN1_SEQUENCE_OF policyInformation_ilc)

let certificatePolicies_expansion
= mk_expansion (DEFAULT ^: critical_field) certificatePolicies_ilc

let id_ce_authorityKeyIdentifier = id_ce /+ 35

let authorityKeyIdentifier_ilc
= ASN1_ILC sequence_id
    (ASN1_SEQUENCE (|[
      OPTION ^: (ASN1_ILC (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 0) (ASN1_TERMINAL ASN1_OCTETSTRING));
      OPTION ^: (ASN1_ILC (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 1) generalNames_c);
      OPTION ^: (ASN1_ILC (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 2) (ASN1_TERMINAL ASN1_INTEGER))], _|))

let authorityKeyIdentifier_expansion
= mk_expansion (DEFAULT ^: critical_field_MUST_false) authorityKeyIdentifier_ilc

let id_ce_extKeyUsage = id_ce /+ 37

let extKeyUsageSyntax_ilc
= ASN1_ILC sequence_id (ASN1_SEQUENCE_OF (ASN1_ILC oid_id (ASN1_TERMINAL ASN1_OID)))

let extKeyUsage_expansion
= mk_expansion (DEFAULT ^: critical_field) extKeyUsageSyntax_ilc

let supported_extensions 
= [(id_pe_authorityInformationAccess, authorityInformationAcess_expansion);
   (id_ce_subjectKeyIdentifier, subjectKeyIdentifier_expansion);
   (id_ce_keyUsage, keyUsage_expansion);
   (id_ce_subjectAlternativeName, subjectAlternativeName_expansion);
   (id_ce_basicConstraints, basicConstraints_expansion);
   (id_ce_cRLDistributionPoints, cRLDistributionPoints_expansion);
   (id_ce_certificatePolicies, certificatePolicies_expansion);
   (id_ce_authorityKeyIdentifier, authorityKeyIdentifier_expansion);
   (id_ce_extKeyUsage, extKeyUsage_expansion)]

let extnValue_fallback_ilc
= ASN1_ILC octet_string_id (ASN1_TERMINAL ASN1_OCTETSTRING)

let extension_fallback_with_pf : asn1_gen_items_k
= (|[ DEFAULT ^: critical_field_MUST_false;
      PLAIN ^: extnValue_fallback_ilc], _|)

let extension_ilc
= ASN1_ILC sequence_id
    (ASN1_ANY_OID oid_id supported_extensions (Some extension_fallback_with_pf) (assert (List.noRepeats (List.map fst supported_extensions)) by (Tactics.trivial ())))

let extensions_ilc' 
= ASN1_ILC sequence_id (ASN1_SEQUENCE_OF extension_ilc)

let extensions_id = mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3

let extensions_ilc
= ASN1_ILC extensions_id (ASN1_PREFIXED extensions_ilc')

// WHY WHY WHY
let map_tags (items : list asn1_gen_item_k) =
  List.map (fun x -> let (| s, d, _|) = x in (s, d)) items

#push-options "--max_fuel 16"

let fields = [
      PLAIN ^: version_field;
      PLAIN ^: serialNumber_ilc;
      PLAIN ^: signature_ilc;
      PLAIN ^: issuer_ilc;
      PLAIN ^: validity_ilc;
      PLAIN ^: subject_ilc;
      PLAIN ^: subjectPublicKeyInfo_ilc;
      OPTION ^: issuerUniqueId_ilc;
      OPTION ^: subjectUniqueId_ilc;
      PLAIN ^: extensions_ilc]

let tags = map_tags fields

let pf : squash (asn1_sequence_k_wf tags) = assert (asn1_sequence_k_wf tags) by (Tactics.compute() ; Tactics.smt())

let x509_TBSCertificate_ilc
= ASN1_ILC sequence_id 
    (ASN1_SEQUENCE (|fields, pf|))

#pop-options

let signatureAlgorithm_ilc = algorithmIdentifier_ilc

let signatureValue_ilc
= ASN1_ILC bit_string_id (ASN1_TERMINAL ASN1_BITSTRING)

let x509_certificate_ilc
= let fields = [
      PLAIN ^: x509_TBSCertificate_ilc;
      PLAIN ^: signatureAlgorithm_ilc;
      PLAIN ^: signatureValue_ilc] in
  let tags = map_tags fields in
  let pf : squash (asn1_sequence_k_wf tags) = assert (asn1_sequence_k_wf tags) by
(Tactics.compute(); Tactics.smt()) in
  ASN1_ILC sequence_id
    (ASN1_SEQUENCE (|fields, pf|))

// let's go boom!

open ASN1.Spec.Interpreter

let x509_certificate_parser = asn1_as_parser x509_certificate_ilc


[@@normalize_for_extraction [delta;
                             zeta;
                             iota;
                             primops]]
let parse_cert (b:bytes) = x509_certificate_parser b
