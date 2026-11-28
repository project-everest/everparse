module ASN1.Pulse.X509
#lang-pulse
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Interpreter
module LPS = LowParse.Pulse.Base

(* Extraction roots: C validators for X.509 certificates and CRLs *)

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.X509"; "ASN1.UniversalTypes"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_certificate : LPS.validator #(asn1_t ASN1.X509.x509_certificate) #asn1_strong_parser_kind (asn1_as_parser ASN1.X509.x509_certificate) =
  validate_k ASN1.X509.x509_certificate (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.CRL"; "ASN1.X509"; "ASN1.UniversalTypes"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_crl : LPS.validator #(asn1_t ASN1.CRL.cRLCertificateList) #asn1_strong_parser_kind (asn1_as_parser ASN1.CRL.cRLCertificateList) =
  validate_k ASN1.CRL.cRLCertificateList (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))
