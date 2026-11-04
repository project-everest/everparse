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
open ASN1.Syntax

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

module DC = ASN1.DiffTest.Constructed

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Constructed"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_choice_ : aparser #(asn1_impl_t DC.choice) #(asn1_t DC.choice) (asn1_rel DC.choice) #asn1_strong_parser_kind (asn1_as_parser DC.choice) =
  fun input #pm #w #v -> parse_k DC.choice (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v


(* SEQUENCE { a INTEGER } and SEQUENCE { a INTEGER, b BOOLEAN } *)
noextract
let seqA = ASN1.Syntax.asn1_sequence [ "a" *^ (PLAIN ^: ASN1.Syntax.asn1_integer) ] (_ by (ASN1.Syntax.seq_tac ()))
noextract
let seqAB = ASN1.Syntax.asn1_sequence [ "a" *^ (PLAIN ^: ASN1.Syntax.asn1_integer); "b" *^ (PLAIN ^: ASN1.Syntax.asn1_boolean) ] (_ by (ASN1.Syntax.seq_tac ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Constructed"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_seqA : aparser #(asn1_impl_t seqA) #(asn1_t seqA) (asn1_rel seqA) #asn1_strong_parser_kind (asn1_as_parser seqA) =
  fun input #pm #w #v -> parse_k seqA (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Constructed"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_seqAB : aparser #(asn1_impl_t seqAB) #(asn1_t seqAB) (asn1_rel seqAB) #asn1_strong_parser_kind (asn1_as_parser seqAB) =
  fun input #pm #w #v -> parse_k seqAB (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Constructed"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer];
  zeta; iota; primops]]
let parse_seq : aparser #(asn1_impl_t DC.seq) #(asn1_t DC.seq) (asn1_rel DC.seq) #asn1_strong_parser_kind (asn1_as_parser DC.seq) =
  fun input #pm #w #v -> parse_k DC.seq (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

(* SEQUENCE OF INTEGER and SET OF OCTET STRING *)
noextract
let seqOfInt = ASN1.Syntax.asn1_sequence_of ASN1.Syntax.asn1_integer
noextract
let setOfOctets = ASN1.Syntax.asn1_set_of ASN1.Syntax.asn1_octetstring

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml];
  zeta; iota; primops]]
let parse_seqOfInt : aparser #(asn1_impl_t seqOfInt) #(asn1_t seqOfInt) (asn1_rel seqOfInt) #asn1_strong_parser_kind (asn1_as_parser seqOfInt) =
  fun input #pm #w #v -> parse_k seqOfInt (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml];
  zeta; iota; primops]]
let parse_setOfOctets : aparser #(asn1_impl_t setOfOctets) #(asn1_t setOfOctets) (asn1_rel setOfOctets) #asn1_strong_parser_kind (asn1_as_parser setOfOctets) =
  fun input #pm #w #v -> parse_k setOfOctets (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

(* SET { b BOOLEAN, a [0] IMPLICIT INTEGER OPTIONAL, c [1] IMPLICIT OCTET STRING },
   whose components are declared in canonical order *)
noextract
let setBAC = ASN1.Syntax.asn1_set [
    "b" *^ (PLAIN ^: ASN1.Syntax.asn1_boolean);
    "a" *^ (OPTION ^: ASN1.Syntax.mk_retagged (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 0) ASN1.Syntax.asn1_integer);
    "c" *^ (PLAIN ^: ASN1.Syntax.mk_retagged (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1) ASN1.Syntax.asn1_octetstring)]
    (_ by (ASN1.Syntax.set_tac ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml];
  zeta; iota; primops]]
let parse_setBAC : aparser #(asn1_impl_t setBAC) #(asn1_t setBAC) (asn1_rel setBAC) #asn1_strong_parser_kind (asn1_as_parser setBAC) =
  fun input #pm #w #v -> parse_k setBAC (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

(* ANY DEFINED BY (OBJECT IDENTIFIER keys) *)

noextract
let oid123 = ASN1.Syntax.mk_oid [1; 2; 3]
noextract
let oid124 = ASN1.Syntax.mk_oid [1; 2; 4]
noextract
let params_null = ASN1.Syntax.mk_gen_items ["p" *^ (PLAIN ^: ASN1.Syntax.asn1_null)] (_ by (ASN1.Syntax.seq_tac ()))
noextract
let params_int = ASN1.Syntax.mk_gen_items ["p" *^ (PLAIN ^: ASN1.Syntax.asn1_integer)] (_ by (ASN1.Syntax.seq_tac ()))
noextract
let params_any = ASN1.Syntax.mk_gen_items ["p" *^ (OPTION ^: ASN1.Syntax.asn1_any)] (_ by (ASN1.Syntax.seq_tac ()))

(* SEQUENCE { v INTEGER, alg OBJECT IDENTIFIER, p ANY DEFINED BY alg }
   with 1.2.3 -> NULL, 1.2.4 -> INTEGER, no fallback *)
noextract
let adbP = ASN1.Syntax.asn1_any_oid_prefix
  ["v" *^ (PLAIN ^: ASN1.Syntax.asn1_integer)]
  "alg"
  [(oid123, params_null); (oid124, params_int)]
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ()))

(* SEQUENCE { alg OBJECT IDENTIFIER, p ANY DEFINED BY alg OPTIONAL }
   with 1.2.3 -> NULL, 1.2.4 -> INTEGER, and a fallback *)
noextract
let adbF = ASN1.Syntax.asn1_any_oid_with_fallback
  "alg"
  [(oid123, params_null); (oid124, params_int)]
  params_any
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.DiffTest.Any"; "ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t];
  zeta; iota; primops]]
let parse_algId : aparser #(asn1_impl_t ASN1.DiffTest.Any.algId) #(asn1_t ASN1.DiffTest.Any.algId) (asn1_rel ASN1.DiffTest.Any.algId) #asn1_strong_parser_kind (asn1_as_parser ASN1.DiffTest.Any.algId) =
  fun input #pm #w #v -> parse_k ASN1.DiffTest.Any.algId (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t];
  zeta; iota; primops]]
let parse_adbP : aparser #(asn1_impl_t adbP) #(asn1_t adbP) (asn1_rel adbP) #asn1_strong_parser_kind (asn1_as_parser adbP) =
  fun input #pm #w #v -> parse_k adbP (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t];
  zeta; iota; primops]]
let parse_adbF : aparser #(asn1_impl_t adbF) #(asn1_t adbF) (asn1_rel adbF) #asn1_strong_parser_kind (asn1_as_parser adbF) =
  fun input #pm #w #v -> parse_k adbF (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

(* ANY DEFINED BY with keys other than OBJECT IDENTIFIER: the key is
   compared byte-for-byte with its DER content encoding *)

(* SEQUENCE { k OCTET STRING, p ANY DEFINED BY k OPTIONAL }
   with 'AA'H -> NULL, 'AABB'H -> INTEGER, and a fallback *)
noextract
let adbO = ASN1_ILC ASN1.Syntax.sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) ASN1.Syntax.octetstring_id ASN1_OCTETSTRING
  [([0xAAuy], params_null); ([0xAAuy; 0xBBuy], params_int)] (Some params_any)
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ())))

(* SEQUENCE { v INTEGER, k BOOLEAN, p ANY DEFINED BY k }
   with TRUE -> INTEGER, FALSE -> NULL, no fallback *)
noextract
let adbB = ASN1_ILC ASN1.Syntax.sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l ["v" *^ (PLAIN ^: ASN1.Syntax.asn1_integer)]) ASN1.Syntax.boolean_id ASN1_BOOLEAN
  [(true, params_int); (false, params_null)] None
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ())))

(* SEQUENCE { k PrintableString, p ANY DEFINED BY k }
   with "ab" -> INTEGER, "a" -> NULL, no fallback *)
noextract
let adbS = ASN1_ILC ASN1.Syntax.sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) ASN1.Syntax.printablestring_id ASN1_PRINTABLESTRING
  [([0x61uy; 0x62uy], params_int); ([0x61uy], params_null)] None
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ())))

(* SEQUENCE { k INTEGER, p ANY DEFINED BY k OPTIONAL }
   with 1 -> NULL, -1 -> INTEGER, 2^64 (a 9-byte key) -> NULL, and a fallback *)
noextract
let adbI = ASN1_ILC ASN1.Syntax.sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) ASN1.Syntax.integer_id (ASN1_INTEGER asn1_any_integer_bound)
  [([0x01uy], params_null); ([0xFFuy], params_int); (ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0x01uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy] (_ by (ASN1.Syntax.wf_tac ())), params_null)] (Some params_any)
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ())))

(* SEQUENCE { k [0] EXPLICIT INTEGER, p ANY DEFINED BY k }
   with 1 -> NULL, -1 -> INTEGER, no fallback: the tagged key is compared
   structurally (inner identifier, DER length, then content bytes) *)
noextract
let adbT = ASN1_ILC ASN1.Syntax.sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) (ASN1_PREFIXED_TERMINAL ASN1.Syntax.integer_id (ASN1_INTEGER asn1_any_integer_bound))
  [([0x01uy], params_null); ([0xFFuy], params_int)] None
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ())))

(* SEQUENCE {
     a INTEGER DEFAULT 0,
     b OCTET STRING DEFAULT 'ABCD'H,
     s PrintableString DEFAULT "ab",
     t [0] EXPLICIT INTEGER DEFAULT 5,
     r [1] IMPLICIT INTEGER (0..10) DEFAULT 3 }
   DEFAULT values are literals, compared like ANY DEFINED BY keys: a
   present item encoding its default value is rejected *)
noextract
let defL = ASN1.Syntax.asn1_sequence [
    "a" *^ (DEFAULT ^: ASN1.Syntax.mk_default_field ASN1.Syntax.asn1_integer (ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0x00uy] (_ by (ASN1.Syntax.wf_tac ()))));
    "b" *^ (DEFAULT ^: ASN1.Syntax.mk_default_field ASN1.Syntax.asn1_octetstring [0xABuy; 0xCDuy]);
    "s" *^ (DEFAULT ^: ASN1.Syntax.mk_default_field ASN1.Syntax.asn1_printablestring [0x61uy; 0x62uy]);
    "t" *^ (DEFAULT ^: ASN1_DEFAULT_TERMINAL (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) #(ASN1_PREFIXED_TERMINAL ASN1.Syntax.integer_id (ASN1_INTEGER asn1_any_integer_bound))
      (ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0x05uy] (_ by (ASN1.Syntax.wf_tac ()))));
    "r" *^ (DEFAULT ^: ASN1.Syntax.mk_restriction_default_field (ASN1.Syntax.mk_retagged (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1) ASN1.Syntax.asn1_integer) (RESTRICT_INT_RANGE (Some 0) (Some 10))
      (ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0x03uy] (_ by (ASN1.Syntax.wf_tac ()))))]
  (_ by (ASN1.Syntax.seq_tac ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t];
  zeta; iota; primops]]
let parse_adbO : aparser #(asn1_impl_t adbO) #(asn1_t adbO) (asn1_rel adbO) #asn1_strong_parser_kind (asn1_as_parser adbO) =
  fun input #pm #w #v -> parse_k adbO (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t];
  zeta; iota; primops]]
let parse_adbB : aparser #(asn1_impl_t adbB) #(asn1_t adbB) (asn1_rel adbB) #asn1_strong_parser_kind (asn1_as_parser adbB) =
  fun input #pm #w #v -> parse_k adbB (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t];
  zeta; iota; primops]]
let parse_adbS : aparser #(asn1_impl_t adbS) #(asn1_t adbS) (asn1_rel adbS) #asn1_strong_parser_kind (asn1_as_parser adbS) =
  fun input #pm #w #v -> parse_k adbS (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t];
  zeta; iota; primops]]
let parse_adbI : aparser #(asn1_impl_t adbI) #(asn1_t adbI) (asn1_rel adbI) #asn1_strong_parser_kind (asn1_as_parser adbI) =
  fun input #pm #w #v -> parse_k adbI (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t];
  zeta; iota; primops]]
let parse_adbT : aparser #(asn1_impl_t adbT) #(asn1_t adbT) (asn1_rel adbT) #asn1_strong_parser_kind (asn1_as_parser adbT) =
  fun input #pm #w #v -> parse_k adbT (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_adbO : LowParse.Pulse.Base.validator #(asn1_t adbO) #asn1_strong_parser_kind (asn1_as_parser adbO) =
  validate_k adbO (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_adbB : LowParse.Pulse.Base.validator #(asn1_t adbB) #asn1_strong_parser_kind (asn1_as_parser adbB) =
  validate_k adbB (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_adbS : LowParse.Pulse.Base.validator #(asn1_t adbS) #asn1_strong_parser_kind (asn1_as_parser adbS) =
  validate_k adbS (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_adbI : LowParse.Pulse.Base.validator #(asn1_t adbI) #asn1_strong_parser_kind (asn1_as_parser adbI) =
  validate_k adbI (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_adbT : LowParse.Pulse.Base.validator #(asn1_t adbT) #asn1_strong_parser_kind (asn1_as_parser adbT) =
  validate_k adbT (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t];
  zeta; iota; primops]]
let parse_defL : aparser #(asn1_impl_t defL) #(asn1_t defL) (asn1_rel defL) #asn1_strong_parser_kind (asn1_as_parser defL) =
  fun input #pm #w #v -> parse_k defL (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_defL : LowParse.Pulse.Base.validator #(asn1_t defL) #asn1_strong_parser_kind (asn1_as_parser defL) =
  validate_k defL (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))

(* SET { c [1] IMPLICIT OCTET STRING,
         a [0] IMPLICIT INTEGER OPTIONAL,
         b INTEGER DEFAULT 0 }
   whose components are declared in the reverse of the canonical order of
   their tags: the parser dispatches each encoded element to its component
   by its tag *)
noextract
let setCAB = ASN1.Syntax.asn1_set [
    "c" *^ (PLAIN ^: ASN1.Syntax.mk_retagged (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1) ASN1.Syntax.asn1_octetstring);
    "a" *^ (OPTION ^: ASN1.Syntax.mk_retagged (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 0) ASN1.Syntax.asn1_integer);
    "b" *^ (DEFAULT ^: ASN1.Syntax.mk_default_field ASN1.Syntax.asn1_integer (ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0x00uy] (_ by (ASN1.Syntax.wf_tac ()))))]
    (_ by (ASN1.Syntax.set_tac ()))

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml];
  zeta; iota; primops]]
let parse_setCAB : aparser #(asn1_impl_t setCAB) #(asn1_t setCAB) (asn1_rel setCAB) #asn1_strong_parser_kind (asn1_as_parser setCAB) =
  fun input #pm #w #v -> parse_k setCAB (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ())) input #pm #w #v

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.ParseTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map; `%ASN1.Pulse.Interpreter.all_defaultable];
  zeta; iota; primops]]
let validate_setCAB : LowParse.Pulse.Base.validator #(asn1_t setCAB) #asn1_strong_parser_kind (asn1_as_parser setCAB) =
  validate_k setCAB (_ by (FStar.Tactics.norm [delta; zeta; iota; primops]; FStar.Tactics.trivial ()))
