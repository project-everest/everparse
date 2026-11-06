module ASN1.Pulse.DiffTest.Smoke
#lang-pulse
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Interpreter
module S = Pulse.Lib.Slice
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module LPS = LowParse.Pulse.Base
module Smoke = ASN1.DiffTest.Smoke

let smoke_supported () : squash (supported_k Smoke.smoke) =
  _ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Smoke"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_smoke : LPS.validator #(asn1_t Smoke.smoke) #asn1_strong_parser_kind (asn1_as_parser Smoke.smoke) =
  validate_k Smoke.smoke (smoke_supported ())
