module ASN1.Pulse.CheckedWriteTest
#lang-pulse
open Pulse.Lib.Pervasives
open ASN1.Base
open ASN1.Spec.Interpreter
open ASN1.Spec.Relax
open ASN1.Pulse.Rel
open ASN1.Pulse.Interpreter
open ASN1.Pulse.CheckedWriter
open ASN1.Syntax

(* Extraction roots: checked right-to-left writers (ASN1.Pulse.CheckedWriter)
   for schemas with constraints that the relaxed schemas do not enforce:
   DEFAULT components, value restrictions, an implicitly tagged string,
   a small INTEGER bound, SIZE (1..MAX), SET OF order; and ANY DEFINED BY
   with keys of various kinds *)

(* SEQUENCE { a INTEGER DEFAULT 0, b OCTET STRING DEFAULT 'ABCD'H,
   s PrintableString DEFAULT "ab", t [0] INTEGER DEFAULT 5,
   r [1] IMPLICIT INTEGER (0..10) DEFAULT 3 } *)
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

noextract
let defL_ok : squash (checked_ok defL) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_defL : checked_writer_t defL defL_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k defL defL_ok 1.0R (relaxed_writer defL defL_ok 1.0R) (validator defL defL_ok) x' #y out pos #v #p

(* SEQUENCE { i [0] IMPLICIT IA5String, r INTEGER (0..10), s INTEGER (-128..127) } *)
noextract
let tagS = ASN1.Syntax.asn1_sequence [
    "i" *^ (PLAIN ^: ASN1.Syntax.mk_retagged (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 0) ASN1.Syntax.asn1_ia5string);
    "r" *^ (PLAIN ^: ASN1.Syntax.mk_restriction_field ASN1.Syntax.asn1_integer (RESTRICT_INT_RANGE (Some 0) (Some 10)));
    "s" *^ (PLAIN ^: ASN1.Syntax.asn1_bounded_integer 1)]
  (_ by (ASN1.Syntax.seq_tac ()))

noextract
let tagS_ok : squash (checked_ok tagS) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_tagS : checked_writer_t tagS tagS_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k tagS tagS_ok 1.0R (relaxed_writer tagS tagS_ok 1.0R) (validator tagS tagS_ok) x' #y out pos #v #p

(* SEQUENCE SIZE (1..MAX) OF INTEGER *)
noextract
let neSeqOfInt = ASN1.Syntax.asn1_nonempty_sequence_of ASN1.Syntax.asn1_integer

noextract
let neSeqOfInt_ok : squash (checked_ok neSeqOfInt) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_neSeqOfInt : checked_writer_t neSeqOfInt neSeqOfInt_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k neSeqOfInt neSeqOfInt_ok 1.0R (relaxed_writer neSeqOfInt neSeqOfInt_ok 1.0R) (validator neSeqOfInt neSeqOfInt_ok) x' #y out pos #v #p

(* SET OF OCTET STRING *)
noextract
let setOfOctets = ASN1.Syntax.asn1_set_of ASN1.Syntax.asn1_octetstring

noextract
let setOfOctets_ok : squash (checked_ok setOfOctets) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_setOfOctets : checked_writer_t setOfOctets setOfOctets_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k setOfOctets setOfOctets_ok 1.0R (relaxed_writer setOfOctets setOfOctets_ok 1.0R) (validator setOfOctets setOfOctets_ok) x' #y out pos #v #p

(* SET { b INTEGER DEFAULT 0, a [0] IMPLICIT INTEGER OPTIONAL,
   c [1] IMPLICIT OCTET STRING }, declared in canonical order (as required
   by the writers) *)
noextract
let setBAC = ASN1.Syntax.asn1_set [
    "b" *^ (DEFAULT ^: ASN1.Syntax.mk_default_field ASN1.Syntax.asn1_integer (ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0x00uy] (_ by (ASN1.Syntax.wf_tac ()))));
    "a" *^ (OPTION ^: ASN1.Syntax.mk_retagged (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 0) ASN1.Syntax.asn1_integer);
    "c" *^ (PLAIN ^: ASN1.Syntax.mk_retagged (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC PRIMITIVE 1) ASN1.Syntax.asn1_octetstring)]
    (_ by (ASN1.Syntax.set_tac ()))

noextract
let setBAC_ok : squash (checked_ok setBAC) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_setBAC : checked_writer_t setBAC setBAC_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k setBAC setBAC_ok 1.0R (relaxed_writer setBAC setBAC_ok 1.0R) (validator setBAC setBAC_ok) x' #y out pos #v #p

(* ANY DEFINED BY: the key literals are written as constants, and the
   key and payload are validated after writing, like the rest *)

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

noextract
let adbP_ok : squash (checked_ok adbP) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_adbP : checked_writer_t adbP adbP_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k adbP adbP_ok 1.0R (relaxed_writer adbP adbP_ok 1.0R) (validator adbP adbP_ok) x' #y out pos #v #p

(* SEQUENCE { alg OBJECT IDENTIFIER, p ANY DEFINED BY alg OPTIONAL }
   with 1.2.3 -> NULL, 1.2.4 -> INTEGER, and a fallback *)
noextract
let adbF = ASN1.Syntax.asn1_any_oid_with_fallback
  "alg"
  [(oid123, params_null); (oid124, params_int)]
  params_any
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ()))

noextract
let adbF_ok : squash (checked_ok adbF) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_adbF : checked_writer_t adbF adbF_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k adbF adbF_ok 1.0R (relaxed_writer adbF adbF_ok 1.0R) (validator adbF adbF_ok) x' #y out pos #v #p

(* SEQUENCE { k OCTET STRING, p ANY DEFINED BY k OPTIONAL }
   with 'AA'H -> NULL, 'AABB'H -> INTEGER, and a fallback *)
noextract
let adbO = ASN1_ILC ASN1.Syntax.sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) ASN1.Syntax.octetstring_id ASN1_OCTETSTRING
  [([0xAAuy], params_null); ([0xAAuy; 0xBBuy], params_int)] (Some params_any)
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ())))

noextract
let adbO_ok : squash (checked_ok adbO) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_adbO : checked_writer_t adbO adbO_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k adbO adbO_ok 1.0R (relaxed_writer adbO adbO_ok 1.0R) (validator adbO adbO_ok) x' #y out pos #v #p

(* SEQUENCE { v INTEGER, k BOOLEAN, p ANY DEFINED BY k }
   with TRUE -> INTEGER, FALSE -> NULL, no fallback *)
noextract
let adbB = ASN1_ILC ASN1.Syntax.sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l ["v" *^ (PLAIN ^: ASN1.Syntax.asn1_integer)]) ASN1.Syntax.boolean_id ASN1_BOOLEAN
  [(true, params_int); (false, params_null)] None
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ())))

noextract
let adbB_ok : squash (checked_ok adbB) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_adbB : checked_writer_t adbB adbB_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k adbB adbB_ok 1.0R (relaxed_writer adbB adbB_ok 1.0R) (validator adbB adbB_ok) x' #y out pos #v #p

(* SEQUENCE { k INTEGER, p ANY DEFINED BY k OPTIONAL }
   with 1 -> NULL, -1 -> INTEGER, 2^64 (a 9-byte key) -> NULL, and a fallback *)
noextract
let adbI = ASN1_ILC ASN1.Syntax.sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) ASN1.Syntax.integer_id (ASN1_INTEGER asn1_any_integer_bound)
  [(ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0x01uy] (_ by (ASN1.Syntax.wf_tac ())), params_null); (ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0xFFuy] (_ by (ASN1.Syntax.wf_tac ())), params_int); (ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0x01uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy] (_ by (ASN1.Syntax.wf_tac ())), params_null)] (Some params_any)
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ())))

noextract
let adbI_ok : squash (checked_ok adbI) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_adbI : checked_writer_t adbI adbI_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k adbI adbI_ok 1.0R (relaxed_writer adbI adbI_ok 1.0R) (validator adbI adbI_ok) x' #y out pos #v #p

(* SEQUENCE { k [0] EXPLICIT INTEGER, p ANY DEFINED BY k }
   with 1 -> NULL, -1 -> INTEGER, no fallback *)
noextract
let adbT = ASN1_ILC ASN1.Syntax.sequence_id (ASN1_ANY_DEFINED_BY _ (list_as_l []) (ASN1.Syntax.mk_custom_id CONTEXT_SPECIFIC CONSTRUCTED 0) (ASN1_PREFIXED_TERMINAL ASN1.Syntax.integer_id (ASN1_INTEGER asn1_any_integer_bound))
  [(ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0x01uy] (_ by (ASN1.Syntax.wf_tac ())), params_null); (ASN1.Syntax.mk_int_lit asn1_any_integer_bound [0xFFuy] (_ by (ASN1.Syntax.wf_tac ())), params_int)] None
  (_ by (ASN1.Syntax.seq_tac ()))
  (_ by (ASN1.Syntax.choice_tac ())))

noextract
let adbT_ok : squash (checked_ok adbT) = _ by (FStar.Tactics.norm [delta; zeta; iota; primops; simplify]; FStar.Tactics.trivial ())

[@@normalize_for_extraction [
  delta_attr [`%asn1_pulse_attr; `%ASN1.Pulse.Restrict.asn1_restrict_attr; `%asn1_relax_attr];
  delta_namespace ["ASN1.Syntax"; "ASN1.Pulse.CheckedWriteTest"];
  delta_only [`%dfst; `%dsnd; `%Mkdtuple2?._1; `%Mkdtuple2?._2; `%ASN1.Base.k_as_lk; `%ASN1.Base.list_as_l; `%ASN1.Base.mk_ASN1_GEN_ITEM; `%ASN1.Base.proj2_of_3; `%List.Tot.map;
    `%asn1_impl_t; `%asn1_content_impl_t; `%asn1_terminal_impl_t; `%asn1_lc_impl_t; `%asn1_items_impl_t; `%asn1_decorated_impl_t; `%small_integer; `%ml;
    `%asn1_items_any_impl_t; `%asn1_adb_suffix_impl_t;
    `%ASN1.Pulse.Writer.Lemmas.kenc; `%ASN1.Pulse.Interpreter.all_defaultable; `%FStar.Pervasives.coerce_eq; `%ASN1.Base.asn1_any_integer_bound; `%relaxed_writer; `%validator];
  zeta; iota; primops]]
let check_write_adbT : checked_writer_t adbT adbT_ok 1.0R =
  fun x' #y out pos #v #p -> check_write_k adbT adbT_ok 1.0R (relaxed_writer adbT adbT_ok 1.0R) (validator adbT adbT_ok) x' #y out pos #v #p
