module ASN1.Pulse.DiffTest.Prim
#lang-pulse
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Interpreter
module LPS = LowParse.Pulse.Base
module D = ASN1.DiffTest.Prim

(* Extraction roots: one C validator per difftest type of ASN1.DiffTest.Prim *)

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_bool_ : LPS.validator #(asn1_t D.bool_) #asn1_strong_parser_kind (asn1_as_parser D.bool_) =
  validate_k D.bool_ (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_int_ : LPS.validator #(asn1_t D.int_) #asn1_strong_parser_kind (asn1_as_parser D.int_) =
  validate_k D.int_ (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_bits : LPS.validator #(asn1_t D.bits) #asn1_strong_parser_kind (asn1_as_parser D.bits) =
  validate_k D.bits (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_octets : LPS.validator #(asn1_t D.octets) #asn1_strong_parser_kind (asn1_as_parser D.octets) =
  validate_k D.octets (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_null_ : LPS.validator #(asn1_t D.null_) #asn1_strong_parser_kind (asn1_as_parser D.null_) =
  validate_k D.null_ (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_oid : LPS.validator #(asn1_t D.oid) #asn1_strong_parser_kind (asn1_as_parser D.oid) =
  validate_k D.oid (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_relOid : LPS.validator #(asn1_t D.relOid) #asn1_strong_parser_kind (asn1_as_parser D.relOid) =
  validate_k D.relOid (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_desc : LPS.validator #(asn1_t D.desc) #asn1_strong_parser_kind (asn1_as_parser D.desc) =
  validate_k D.desc (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_iri : LPS.validator #(asn1_t D.iri) #asn1_strong_parser_kind (asn1_as_parser D.iri) =
  validate_k D.iri (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_relIri : LPS.validator #(asn1_t D.relIri) #asn1_strong_parser_kind (asn1_as_parser D.relIri) =
  validate_k D.relIri (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_enum_ : LPS.validator #(asn1_t D.enum_) #asn1_strong_parser_kind (asn1_as_parser D.enum_) =
  validate_k D.enum_ (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))
