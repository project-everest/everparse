module ASN1.X509
#push-options "--split_queries no --fuel 2 --ifuel 0"

module U32 = FStar.UInt32
module List = FStar.List.Tot

open ASN1.Base
open ASN1.Syntax

(* Known looseness from rfc5280 section-4:
   . Enforcing version must be 2 (v3)
   . Enforcing extensions must appear
   . Enforced by crypto: the algorithmIdentifier in the signature, subjectPublicKeyInfo, and signatureAlgorithm being consistent
   . Not parsing extension value field of extensions
   . TODO: A list of constants for Name
   . Backward compatibility for Name
   . Only support algorithms and extensions included in the list
*)

// TODO: insert list of supported algorithms here

let pkcs_1 = mk_oid [1;2;840;113549;1;1]

let rSAEncryption_oid = pkcs_1 /+ 1

let md2WithRSAEncryption_oid = mk_oid [1;2;840;113549;1;1;2]

let md5WithRSAEncryption_oid = mk_oid [1;2;840;113549;1;1;4]

let sha_1WithRSAEncryption_oid = mk_oid [1;2;840;113549;1;1;5]

let sha256WithRSAEncryption_oid = mk_oid [1;2;840;113549;1;1;11]

let sha384WithRSAEncryption_oid = pkcs_1 /+ 12

let sha512WithRSAEncryption_oid = pkcs_1 /+ 13

let sha224WithRSAEncryption_oid = pkcs_1 /+ 14

let option_NULL_parameters
= mk_gen_items ["parameters" *^ (OPTION ^: asn1_null)] (_ by (seq_tac ()))

let id_dsa_with_sha1 = mk_oid [1;2;840;10040;4;3]

let omitted_parameters
= mk_gen_items ["parameters" *^ (DEFAULT ^: mk_default_field asn1_null ())] (_ by (seq_tac ()))

let ansi_X9_62 = mk_oid [1;2;840;10045]

let id_ecSigType = ansi_X9_62 /+ 4

let id_ecdsa_with_sha1 = id_ecSigType /+ 1

let id_dsa = mk_oid [1;2;840;10040;4;1]

let dss_parms 
= asn1_sequence 
  ["p" *^ (PLAIN ^: asn1_bounded_integer 200); 
   "q" *^ (PLAIN ^: asn1_bounded_integer 200);
   "g" *^ (PLAIN ^: asn1_bounded_integer 200)]
  (_ by (seq_tac ()))

let dss_parms_field
= mk_gen_items ["parameters" *^ (OPTION ^: dss_parms)] (_ by (seq_tac ()))

let dhpublicnumber = mk_oid [1;2;840;10046;2;1]

let validationParms
= asn1_sequence
  ["seed" *^ (PLAIN ^: asn1_bitstring);
   "pgenCounter" *^ (PLAIN ^: asn1_integer)]
  (_ by (seq_tac ()))

let domainParameters 
= asn1_sequence
  ["p" *^ (PLAIN ^: asn1_integer);
   "g" *^ (PLAIN ^: asn1_integer);
   "q" *^ (PLAIN ^: asn1_integer);
   "j" *^ (OPTION ^: asn1_integer);
   "validationParms" *^ (OPTION ^: validationParms)]
  (_ by (seq_tac ()))

let domainParameters_field
= mk_gen_items ["parameters" *^ (PLAIN ^: domainParameters)] (_ by (seq_tac ()))

let id_keyExchangeAlgorithm = mk_oid [2;16;840;1;101;2;1;1;22]

let kEA_Parms_Id_field
= mk_gen_items ["parameters" *^ (PLAIN ^: asn1_octetstring)] (_ by (seq_tac ()))

let id_public_key_type = ansi_X9_62 /+ 2

let id_ecPublicKey = id_public_key_type /+ 1

let fieldElement = asn1_octetstring

let curve
= asn1_sequence
  ["a" *^ (PLAIN ^: fieldElement);
   "b" *^ (PLAIN ^: fieldElement);
   "seed" *^ (OPTION ^: asn1_bitstring)]
  (_ by (seq_tac ()))

let eCPVer
= mk_restricted_field asn1_integer (fun x -> x = 1)

let id_fieldType = ansi_X9_62 /+ 1

let prime_field_oid = id_fieldType /+ 1

let prime_p
= mk_gen_items ["parameters" *^ (PLAIN ^: asn1_integer)] (_ by (seq_tac ()))

let characteristic_two_field_oid = id_fieldType /+ 2

let id_characteristic_two_basis = characteristic_two_field_oid /+ 1

let gnBasis_oid = id_characteristic_two_basis /+ 1

let gnBasis_parameters
= mk_gen_items [PLAIN ^: asn1_null] (_ by (seq_tac ()))

let tpBasis_oid = id_characteristic_two_basis /+ 2

let tpBasis_parameters
= mk_gen_items ["Trinomial" *^ (PLAIN ^: asn1_integer)] (_ by (seq_tac ()))

let ppBasis_oid = id_characteristic_two_basis /+ 3

let pentanomial
= asn1_sequence [
    "k1" *^ (PLAIN ^: asn1_integer);
    "k2" *^ (PLAIN ^: asn1_integer);
    "k3" *^ (PLAIN ^: asn1_integer)]
    (_ by (seq_tac ()))

let ppBasis_parameters
= mk_gen_items ["Pentanomial" *^ (PLAIN ^: pentanomial)] (_ by (seq_tac ()))

let characteristic_two
= asn1_any_oid_prefix
    ["m" *^ (PLAIN ^: asn1_integer)]
    "basis"
    [(gnBasis_oid, gnBasis_parameters);
     (tpBasis_oid, tpBasis_parameters);
     (ppBasis_oid, ppBasis_parameters)]
    (_ by (seq_tac ()))
    (_ by (choice_tac ()))

let characteristic_two_field
= mk_gen_items ["parameters" *^ (PLAIN ^: characteristic_two)] (_ by (seq_tac ()))

let fieldID
= asn1_any_oid
    "fieldType"
    [(prime_field_oid, prime_p);
     (characteristic_two_field_oid, characteristic_two_field)]
    (_ by (seq_tac ()))
    (_ by (choice_tac ()))

let eCParameters
= asn1_sequence [
    "version" *^ (PLAIN ^: eCPVer);
    "fieldID" *^ (PLAIN ^: fieldID);
    "curve" *^ (PLAIN ^: curve);
    "base" *^ (PLAIN ^: asn1_octetstring);
    "order" *^ (PLAIN ^: asn1_integer);
    "cofactor" *^ (OPTION ^: asn1_integer)]
    (_ by (seq_tac ()))

// Warning: Not filtering with the list of named curves

let ecpkParameters
= asn1_choice [
    "ecParameters" ^* eCParameters;
    "namedCurve" ^* asn1_oid;
    "implicitlyCA" ^* asn1_null]
    (_ by (choice_tac ()))

let ecpkParameters_field
= mk_gen_items ["parameters" *^ (PLAIN ^: ecpkParameters)] (_ by (seq_tac ()))

let supported_algorithms
= [(rSAEncryption_oid, option_NULL_parameters);
   (md2WithRSAEncryption_oid, option_NULL_parameters);
   (md5WithRSAEncryption_oid, option_NULL_parameters);
   (sha_1WithRSAEncryption_oid, option_NULL_parameters);
   (sha256WithRSAEncryption_oid, option_NULL_parameters);
   (sha384WithRSAEncryption_oid, option_NULL_parameters);
   (sha512WithRSAEncryption_oid, option_NULL_parameters);
   (sha224WithRSAEncryption_oid, option_NULL_parameters);
   (id_dsa_with_sha1, omitted_parameters);
   (id_ecdsa_with_sha1, omitted_parameters);
   (id_dsa, dss_parms_field);
   (dhpublicnumber, domainParameters_field);
   (id_keyExchangeAlgorithm, kEA_Parms_Id_field);
   (id_ecPublicKey, ecpkParameters_field)]

let version
= mk_restricted_field asn1_integer (fun x -> x = 2)

let certificateSerialNumber = asn1_integer

let ignoreUnknownCrypto
= mk_gen_items [OPTION ^: asn1_any] (_ by (seq_tac ()))

let algorithmIdentifier
= asn1_any_oid_with_fallback
    "algorithm"
    supported_algorithms
    ignoreUnknownCrypto
    (_ by (seq_tac ()))
    (_ by (choice_tac ()))

let attributeType = asn1_oid

//Warning: backward compatibility

//Warning: a list of constants might be needed here

let directoryString
= asn1_choice [
    "telextexString" ^* asn1_teletexstring;
    "printableString" ^* asn1_printablestring;
    "universalString" ^* asn1_universalstring;
    "utf8String" ^* asn1_utf8string;
    "bmpString" ^* asn1_bMPstring]
    (_ by (choice_tac ()))

let attributeValue = directoryString

let attributeValue_field
= mk_gen_items ["value" *^ (PLAIN ^: attributeValue)] (_ by (seq_tac ()))

let emailAddress_oid = mk_oid [1;2;840;113549;1;9;1]

let emailAddress_field
= mk_gen_items ["value" *^ (PLAIN ^: asn1_ia5string)] (_ by (seq_tac ()))

let unstructuredName_oid = mk_oid [1;2;840;113549;1;9;2]

let pKCS9String 
= asn1_choice [
    "telextexString" ^* asn1_teletexstring;
    "printableString" ^* asn1_printablestring;
    "universalString" ^* asn1_universalstring;
    "utf8String" ^* asn1_utf8string;
    "bmpString" ^* asn1_bMPstring;
    "ia5String" ^* asn1_ia5string]
    (_ by (choice_tac ()))

let unstructuredName_field
= mk_gen_items ["id" *^ (PLAIN ^: pKCS9String)] (_ by (seq_tac ()))

let domainComponent_oid = mk_oid [0;9;2342;19200300;100;1;25]

let domainComponent_field
= mk_gen_items ["value" *^ (PLAIN ^: asn1_ia5string)] (_ by (seq_tac ()))

let attributeTypeAndValue
= asn1_any_oid_with_fallback
    "type"
    [(emailAddress_oid, emailAddress_field);
     (domainComponent_oid, domainComponent_field);
     (unstructuredName_oid, unstructuredName_field)]
    attributeValue_field
    (_ by (seq_tac ()))
    (_ by (choice_tac ()))

let relativeDistinguishedName
= asn1_set_of attributeTypeAndValue

let rDNSequence
= asn1_sequence_of relativeDistinguishedName

let name
= asn1_choice ["rsnSequence" ^* rDNSequence] (_ by (choice_tac ()))

let time
= asn1_choice [
    "utcTime" ^* asn1_utctime;
    "generalTime" ^* asn1_generalizedtime]
    (_ by (choice_tac ()))

let validity
= asn1_sequence [
    "notBefore" *^ (PLAIN ^: time);
    "notAfter" *^ (PLAIN ^: time)]
    (_ by (seq_tac ()))

let subjectPublicKeyInfo
= asn1_sequence [
    "algorithm" *^ (PLAIN ^: algorithmIdentifier);
    "subjectPublicKey" *^ (PLAIN ^: asn1_bitstring)]
    (_ by (seq_tac ()))

let uniqueIdentifier = asn1_bitstring

let id_pkix = mk_oid [1;3;6;1;5;5;7]

let id_pe = id_pkix /+ 1

let id_pe_authorityInformationAccess = id_pe /+ 1

//Warning: Partly using the mitls spec which is loosened from rfc5280
#push-options "--fuel 3 --ifuel 1"
let mk_expansion (critical : asn1_gen_item_k) (#s : _) (value : asn1_k s)
  (pf : squash (asn1_sequence_k_wf [proj2_of_3 critical; (Set.singleton octetstring_id, PLAIN)]))
= let items = [critical; "extnValue" *^ (PLAIN ^: (ASN1_ILC octetstring_id (ASN1_PREFIXED value)))] in
  mk_gen_items items pf
#pop-options

let critical_field
= mk_default_field asn1_boolean false

let critical_field_MUST_false
= mk_restricted_default_field asn1_boolean (fun b -> b = false) false

let critical_field_MUST_true
= mk_restricted_field asn1_boolean (fun b -> b = true)

let id_pe_ipAddrBlocks = id_pe /+ 7

//Can be refined

let iPAddress = asn1_bitstring

let iPAddressRange
= asn1_sequence [
    "min" *^ (PLAIN ^: iPAddress);
    "max" *^ (PLAIN ^: iPAddress)]
    (_ by (seq_tac ()))
    
let iPAddressOrRange
= asn1_choice [
    "addressPrefix" ^* iPAddress;
    "addressRange" ^* iPAddressRange]
    (_ by (choice_tac ()))
    
let iPAddressChoice
= asn1_choice [
    "inherit" ^* asn1_null;
    "addressesOrRanges" ^* (asn1_sequence_of iPAddressOrRange)]
    (_ by (choice_tac ()))

let iPAddressFamily
= asn1_sequence [
    "addressFamily" *^ (PLAIN ^: (mk_restricted_field asn1_octetstring (fun s -> let l = Bytes.length s in 2 <= l && l <= 3)));
    "ipAddressChoice" *^ (PLAIN ^: iPAddressChoice)]
    (_ by (seq_tac ()))

let iPAddrBlocks
= asn1_sequence_of iPAddressFamily

let iPAddrBlocks_expansion
= mk_expansion (DEFAULT ^: critical_field) iPAddrBlocks (_ by (seq_tac ()))

let id_ad = id_pkix /+ 48

let id_ad_caIssuers = id_ad /+ 1

let id_ad_ocsp = id_ad /+ 2

let accessMethod
= mk_restricted_field asn1_oid (fun oid -> oid = id_ad_caIssuers || oid = id_ad_ocsp)

let otherName
= asn1_any_oid_with_fallback
    "type-id"
    []
    (mk_gen_items ["value" *^ (PLAIN ^: (mk_prefixed (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) asn1_any))] (_ by (seq_tac ())))
    (_ by (seq_tac ()))
    (_ by (choice_tac ()))

let generalName
= asn1_choice [
    "otherName" ^* (mk_retagged (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) otherName);
    "rfc822Name" ^* (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1) asn1_ia5string);
    "dNSName" ^* (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 2) asn1_ia5string);
    "directoryName" ^* (mk_prefixed (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 4) name);
    "uniformResourceIdentifier" ^* (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 6) asn1_ia5string);
    "iPAddress" ^* (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 7) asn1_octetstring);
    "registeredID" ^* (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 8) asn1_oid)]
    (_ by (choice_tac ()))

let generalNames = asn1_sequence_of generalName

let accessDescription
= asn1_sequence [
    "accessMethod" *^ (PLAIN ^: asn1_oid);
    "accessLocation" *^ (PLAIN ^: generalName)]
    (_ by (seq_tac ()))

let authorityInfoAccessSyntax = asn1_sequence_of accessDescription

let authorityInformationAccess_expansion
= mk_expansion (DEFAULT ^: critical_field_MUST_false) authorityInfoAccessSyntax (_ by (seq_tac ()))

let id_ce = mk_oid [2;5;29]

let id_ce_subjectKeyIdentifier = id_ce /+ 14

let keyIdentifier = asn1_octetstring

let subjectKeyIdentifier = keyIdentifier

let subjectKeyIdentifier_expansion 
= mk_expansion (DEFAULT ^: critical_field_MUST_false) subjectKeyIdentifier (_ by (seq_tac ()))

let id_ce_keyUsage = id_ce /+ 15

let keyUsage = asn1_bitstring

let keyUsage_expansion
= mk_expansion (DEFAULT ^: critical_field) keyUsage (_ by (seq_tac ()))

let id_ce_subjectAlternativeName = id_ce /+ 17

let subjectAlternativeName_expansion 
= mk_expansion (DEFAULT ^: critical_field) generalNames (_ by (seq_tac ()))

let id_ce_basicConstraints = id_ce /+ 19

let basicConstraints
= asn1_sequence [
    "cA" *^ (DEFAULT ^: (mk_default_field asn1_boolean false));
    "pathLenConstraint" *^ (OPTION ^: (mk_restricted_field asn1_integer (fun x -> x >= 0)))]
    (_ by (seq_tac ()))

let basicConstraints_expansion
= mk_expansion (DEFAULT ^: critical_field) basicConstraints (_ by (seq_tac ()))

let id_ce_cRLDistributionPoints = id_ce /+ 31

let distributionPointName
= asn1_choice [
    "fullName" ^* (mk_retagged (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) generalNames);
    "nameRelativeToCRLIssuer" ^* (mk_retagged (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 1) relativeDistinguishedName)]
    (_ by (choice_tac ()))

let reasonFlags = asn1_bitstring

let distributionPoint
= asn1_sequence [
    "distributionPoint" *^ (OPTION ^: (mk_prefixed (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) distributionPointName));
    "reasons" *^ (OPTION ^: (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1) reasonFlags));
    "cRLIssuer" *^ (OPTION ^: (mk_retagged (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 2) generalNames))]
    (_ by (seq_tac ()))

let cRLDistributionPoints
= asn1_sequence_of distributionPoint

let cRLDistributionPoints_expansion
= mk_expansion (DEFAULT ^: critical_field) cRLDistributionPoints (_ by (seq_tac ()))

let id_ce_certificatePolicies = id_ce /+ 32

let cPSuri = asn1_ia5string

let cPSuri_field = mk_gen_items ["qualifier" *^ (PLAIN ^: cPSuri)] (_ by (seq_tac ()))

let id_qt = id_pkix /+ 2

let id_qt_cps = id_qt /+ 1

let id_qt_unotice = id_qt /+ 2

// Warning: Not enforcing the length

let displayText
= asn1_choice [
    "ia5String" ^* asn1_ia5string;
    "visibleString" ^* asn1_visiblestring;
    "bmpString" ^* asn1_bMPstring;
    "utf8String" ^* asn1_utf8string]
    (_ by (choice_tac ()))

let noticeReference
= asn1_sequence [
    "organization" *^ (PLAIN ^: displayText);
    "noticeNumbers" *^ (PLAIN ^: (asn1_sequence_of asn1_integer))]
    (_ by (seq_tac ()))

let userNotice
= asn1_sequence [
    "noticeRef" *^ (OPTION ^: noticeReference);
    "explicitText" *^ (OPTION ^: displayText)]
    (_ by (seq_tac ()))

let userNotice_field
= mk_gen_items ["qualifier" *^ (PLAIN ^: userNotice)] (_ by (seq_tac ()))

let supported_policyQualifier
= [(id_qt_cps, cPSuri_field);
   (id_qt_unotice, userNotice_field)]

let policyQualifierInfo
= asn1_any_oid
    "policyQulifierId"
    supported_policyQualifier
    (_ by (seq_tac ()))
    (_ by (choice_tac ()))

let certPolicyId = asn1_oid

let policyInformation
= asn1_sequence [
    "policyIdentifier" *^ (PLAIN ^: certPolicyId);
    "policyQualifiers" *^ (OPTION ^: asn1_sequence_of policyQualifierInfo)]
    (_ by (seq_tac ())) 

let certificatePolicies
= asn1_sequence_of policyInformation

let certificatePolicies_expansion
= mk_expansion (DEFAULT ^: critical_field) certificatePolicies (_ by (seq_tac ()))

let id_ce_authorityKeyIdentifier = id_ce /+ 35

// Warning: Not handling both being present
let authorityKeyIdentifier
= asn1_sequence [
    "KeyIdentifier" *^ (OPTION ^: (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 0) asn1_octetstring));
    "authorityCertIssuer" *^ (OPTION ^: (mk_retagged (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 1) generalNames));
    "authorityCertSerialNumber" *^ (OPTION ^: (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 2) asn1_integer))]
    (_ by (seq_tac ()))

let authorityKeyIdentifier_expansion
= mk_expansion (DEFAULT ^: critical_field_MUST_false) authorityKeyIdentifier (_ by (seq_tac ()))

let id_ce_extKeyUsage = id_ce /+ 37

let extKeyUsageSyntax = asn1_sequence_of asn1_oid
  
let extKeyUsage_expansion
= mk_expansion (DEFAULT ^: critical_field) extKeyUsageSyntax (_ by (seq_tac ()))

let supported_extensions 
= [(id_pe_authorityInformationAccess, authorityInformationAccess_expansion);
   (id_pe_ipAddrBlocks, iPAddrBlocks_expansion);
   (id_ce_subjectKeyIdentifier, subjectKeyIdentifier_expansion);
   (id_ce_keyUsage, keyUsage_expansion);
   (id_ce_subjectAlternativeName, subjectAlternativeName_expansion);
   (id_ce_basicConstraints, basicConstraints_expansion);
   (id_ce_cRLDistributionPoints, cRLDistributionPoints_expansion);
   (id_ce_certificatePolicies, certificatePolicies_expansion);
   (id_ce_authorityKeyIdentifier, authorityKeyIdentifier_expansion);
   (id_ce_extKeyUsage, extKeyUsage_expansion)]

let extension_fallback
= mk_gen_items [
    "critical" *^ (DEFAULT ^: critical_field_MUST_false);
    "extnValue" *^ (PLAIN ^: asn1_octetstring)]
    (_ by (seq_tac ()))

let extension
= asn1_any_oid_with_fallback
    "extnId"
    supported_extensions
    extension_fallback
    (_ by (seq_tac ()))
    (_ by (choice_tac ()))

let extensions
= asn1_sequence_of extension

#push-options "--fuel 0 --z3rlimit_factor 2"
let x509_TBSCertificate
= asn1_sequence [
    "version" *^ (PLAIN ^: (mk_prefixed (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) version));
    "serialNumber" *^ (PLAIN ^: certificateSerialNumber);
    "signature" *^ (PLAIN ^: algorithmIdentifier);
    "issuer" *^ (PLAIN ^: name);
    "validity" *^ (PLAIN ^: validity);
    "subject" *^ (PLAIN ^: name);
    "subjectPublicKeyInfo" *^ (PLAIN ^: subjectPublicKeyInfo);
    "issuerUniqueID" *^ (OPTION ^: (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1) uniqueIdentifier));
    "subjectUniqueID" *^ (OPTION ^: (mk_retagged (mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 2) uniqueIdentifier));
    "extensions" *^ (OPTION ^: (mk_prefixed (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 3) extensions))]
    (_ by (seq_tac ()))

let x509_certificate
= asn1_sequence [
    "tbsCertificate" *^ (PLAIN ^: x509_TBSCertificate);
    "signatureAlgorithm" *^ (PLAIN ^: algorithmIdentifier);
    "signatureValue" *^ (PLAIN ^: asn1_bitstring)]
    (_ by (seq_tac ()))
#pop-options

// let's go boom!

open ASN1.Spec.Interpreter

let x509_certificate_parser = asn1_as_parser x509_certificate


[@@normalize_for_extraction [delta;
                             zeta;
                             iota;
                             primops]]
let parse_cert (b:bytes) = x509_certificate_parser b

[@@normalize_for_extraction [delta;
                             zeta;
                             iota;
                             primops]]
let dparse_cert (b:bytes) = dasn1_as_parser x509_certificate b
#show-options
