module ASN1.CRL

open ASN1.Base
open ASN1.Syntax

module X509 = ASN1.X509

let crlExtension 
= asn1_any_oid_with_fallback
    "extnId"
    []
    X509.extension_fallback
    (_ by (seq_tac ()))
    (_ by (choice_tac ()))

let crlExtensions = asn1_sequence_of crlExtension

let version = mk_restricted_field asn1_integer (fun x -> x = 1)

let revokedCertificate
= asn1_sequence [
    "userCertificate" *^ (PLAIN ^: X509.certificateSerialNumber);
    "revocationDate" *^ (PLAIN ^: X509.time);
    "crlEntryExtensions" *^ (OPTION ^: crlExtensions)]
    (_ by (seq_tac ()))

let revokedCertificates = asn1_sequence_of revokedCertificate

let tBSCertList 
= asn1_sequence [
    "version" *^ (PLAIN ^: version);
    "signature" *^ (PLAIN ^: X509.algorithmIdentifier);
    "issuer" *^ (PLAIN ^: X509.name);
    "thisUpdate" *^ (PLAIN ^: X509.time);
    "nextUpdate" *^ (OPTION ^: X509.time);
    "revokedCertificates" *^ (OPTION ^: revokedCertificates);
    "crlExtensions" *^ (OPTION ^: mk_prefixed (mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) crlExtensions)]
    (_ by (seq_tac ()))

let cRLCertificateList
= asn1_sequence [
    "tbsCertList" *^ (PLAIN ^: tBSCertList);
    "signatureAlgorithm" *^ (PLAIN ^: X509.algorithmIdentifier);
    "signatureValue" *^ (PLAIN ^: asn1_bitstring)]
    (_ by (seq_tac ()))

open ASN1.Spec.Interpreter

let crl_parser = asn1_as_parser cRLCertificateList


[@@normalize_for_extraction [delta;
                             zeta;
                             iota;
                             primops]]
let parse_crl (b:bytes) = crl_parser b

[@@normalize_for_extraction [delta;
                             zeta;
                             iota;
                             primops]]
let dparse_crl (b:bytes) = dasn1_as_parser cRLCertificateList b

