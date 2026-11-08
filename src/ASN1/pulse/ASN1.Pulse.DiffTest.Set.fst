module ASN1.Pulse.DiffTest.Set
#lang-pulse
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Pulse.Interpreter
module LPS = LowParse.Pulse.Base
module D = ASN1.DiffTest.Set

(* Extraction roots: one C validator per difftest type of
   ASN1.DiffTest.Set *)

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Set"; "ASN1.Syntax"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_set : LPS.validator #(asn1_t D.set_) #asn1_strong_parser_kind (asn1_as_parser D.set_) =
  validate_k D.set_ (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))
