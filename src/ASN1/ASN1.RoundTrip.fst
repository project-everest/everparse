module ASN1.RoundTrip

(* Spec serializers of the X.509 certificate and CRL schemas, extracted to
   OCaml so that ocaml/ASN1_Parser.ml can check, on every successfully
   parsed input, that re-serializing the parsed value yields back the bytes
   consumed by the parser (ASN1.Spec.Serializer.asn1_as_parser_consumed.) *)

open LowParse.Tot.Base
open ASN1.Base

let enc_cert (x: asn1_t ASN1.X509.x509_certificate) : Tot bytes =
  ASN1.Spec.Serializer.asn1_enc ASN1.X509.x509_certificate x

let enc_crl (x: asn1_t ASN1.CRL.cRLCertificateList) : Tot bytes =
  ASN1.Spec.Serializer.asn1_enc ASN1.CRL.cRLCertificateList x
