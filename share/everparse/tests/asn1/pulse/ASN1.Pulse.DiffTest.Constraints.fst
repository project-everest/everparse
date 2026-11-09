module ASN1.Pulse.DiffTest.Constraints
#lang-pulse
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Interpreter
module LPS = LowParse.Pulse.Base
module D = ASN1.DiffTest.Constraints

(* Extraction roots: one C validator per difftest type of
   ASN1.DiffTest.Constraints *)

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Constraints"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_sized : LPS.validator #(asn1_t D.sized) #asn1_strong_parser_kind (asn1_as_parser D.sized) =
  validate_k D.sized (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Constraints"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_byte : LPS.validator #(asn1_t D.byte) #asn1_strong_parser_kind (asn1_as_parser D.byte) =
  validate_k D.byte (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Constraints"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_nonEmptySeqOf : LPS.validator #(asn1_t D.nonEmptySeqOf) #asn1_strong_parser_kind (asn1_as_parser D.nonEmptySeqOf) =
  validate_k D.nonEmptySeqOf (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Constraints"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_nonEmptySetOf : LPS.validator #(asn1_t D.nonEmptySetOf) #asn1_strong_parser_kind (asn1_as_parser D.nonEmptySetOf) =
  validate_k D.nonEmptySetOf (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))
