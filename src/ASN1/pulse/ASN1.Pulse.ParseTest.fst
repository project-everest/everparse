module ASN1.Pulse.ParseTest
#lang-pulse
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Rel
open ASN1.Pulse.Parse
open ASN1.Pulse.Interpreter
open ASN1.Pulse.Parser
module D = ASN1.DiffTest.Prim

(* Extraction roots: zero-copy parsers for some difftest types *)

noextract
let int64_ = ASN1.Syntax.asn1_bounded_integer 8

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_int64 : aparser #(asn1_impl_t int64_) #(asn1_t int64_) (asn1_rel int64_) #asn1_strong_parser_kind (asn1_as_parser int64_) =
  fun input #pm #w #v -> parse_k int64_ (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_int_ : aparser #(asn1_impl_t D.int_) #(asn1_t D.int_) (asn1_rel D.int_) #asn1_strong_parser_kind (asn1_as_parser D.int_) =
  fun input #pm #w #v -> parse_k D.int_ (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_enum_ : aparser #(asn1_impl_t D.enum_) #(asn1_t D.enum_) (asn1_rel D.enum_) #asn1_strong_parser_kind (asn1_as_parser D.enum_) =
  fun input #pm #w #v -> parse_k D.enum_ (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_bits : aparser #(asn1_impl_t D.bits) #(asn1_t D.bits) (asn1_rel D.bits) #asn1_strong_parser_kind (asn1_as_parser D.bits) =
  fun input #pm #w #v -> parse_k D.bits (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_bool_ : aparser #(asn1_impl_t D.bool_) #(asn1_t D.bool_) (asn1_rel D.bool_) #asn1_strong_parser_kind (asn1_as_parser D.bool_) =
  fun input #pm #w #v -> parse_k D.bool_ (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Prim"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_octets : aparser #(asn1_impl_t D.octets) #(asn1_t D.octets) (asn1_rel D.octets) #asn1_strong_parser_kind (asn1_as_parser D.octets) =
  fun input #pm #w #v -> parse_k D.octets (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v
