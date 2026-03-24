module LowParseExample9
#lang-pulse
include LowParseExample9.Aux
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open LowParse.Spec.Base

module LPS = LowParse.Pulse.Base
module LPI = LowParse.Pulse.Int
module LPC = LowParse.Pulse.Combinators
module PPC = LowParse.PulseParse.Combinators
module PPS = LowParse.PulseParse.Sum
module I32 = FStar.Int32

(* Pulse validators for known dsum cases *)

inline_for_extraction noextract
let pulse_validate_tt_cases (x: dsum_known_key tt_sum)
: Tot (LPS.validator (dsnd (parse_tt_cases x)))
= match x with
  | Ka -> (LPI.validate_u8 <: LPS.validator (dsnd (parse_tt_cases Ka)))
  | Kb -> (LPI.validate_u16 <: LPS.validator (dsnd (parse_tt_cases Kb)))
  | _ -> PPC.validate_false ()

inline_for_extraction noextract
let pulse_jump_tt_cases (x: dsum_known_key tt_sum)
: Tot (LPS.jumper (dsnd (parse_tt_cases x)))
= match x with
  | Ka -> (LPI.jump_u8 <: LPS.jumper (dsnd (parse_tt_cases Ka)))
  | Kb -> (LPI.jump_u16 <: LPS.jumper (dsnd (parse_tt_cases Kb)))
  | _ -> LPS.jump_constant_size parse_false 0sz

(* validate_t and jump_t use validate/jump_dsum_cases' for the inner dsum,
   then compose_context + synth for the outer wrapping *)

inline_for_extraction noextract
let parse_dsum_cases_eq_forall (k: maybe_enum_key kt_enum)
: Lemma (forall x . parse (parse_dsum_cases' tt_sum parse_tt_cases parse_u32 k) x == parse (parse_dsum_cases tt_sum parse_tt_cases parse_u32 k) x)
= Classical.forall_intro (parse_dsum_cases_eq' tt_sum parse_tt_cases parse_u32 k)

inline_for_extraction noextract
let validate_dsum_case_for_compose (k: maybe_enum_key kt_enum)
: Tot (LPS.validator (parse_dsum_cases tt_sum parse_tt_cases parse_u32 k))
= parse_dsum_cases_eq_forall k;
  LPS.validate_ext
    (PPS.validate_dsum_cases' tt_sum parse_tt_cases pulse_validate_tt_cases LPI.validate_u32 k)
    (parse_dsum_cases tt_sum parse_tt_cases parse_u32 k)

noextract let validate_t (k: kt) : Tot (LPS.validator (parse_t k)) =
  lemma_synth_kt_inj ();
  PPC.validate_synth
    (PPC.validate_compose_context synth_kt_inv (refine_with_tag key_of_tt)
      (parse_dsum_cases tt_sum parse_tt_cases parse_u32)
      validate_dsum_case_for_compose
      k)
    (synth_t k)

inline_for_extraction noextract
let jump_dsum_case_for_compose (k: maybe_enum_key kt_enum)
: Tot (LPS.jumper (parse_dsum_cases tt_sum parse_tt_cases parse_u32 k))
= parse_dsum_cases_eq_forall k;
  LPS.jump_ext
    (PPS.jump_dsum_cases' tt_sum parse_tt_cases pulse_jump_tt_cases LPI.jump_u32 k)
    (parse_dsum_cases tt_sum parse_tt_cases parse_u32 k)

noextract let jump_t (k: kt) : Tot (LPS.jumper (parse_t k)) =
  lemma_synth_kt_inj ();
  LPC.jump_synth
    (PPC.jump_compose_context synth_kt_inv (refine_with_tag key_of_tt)
      (parse_dsum_cases tt_sum parse_tt_cases parse_u32)
      jump_dsum_case_for_compose
      k)
    (synth_t k)

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
