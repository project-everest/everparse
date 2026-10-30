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
   a small INTEGER bound, SIZE (1..MAX), SET OF order *)

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
