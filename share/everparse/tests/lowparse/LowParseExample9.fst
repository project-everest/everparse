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

(* validate_t and jump_t: use validate_dsum_cases' with validate_ext,
   wrapped in validate_compose_context + validate_synth,
   matching the Low* pattern *)

inline_for_extraction noextract
let validate_dsum_case (mk: dsum_key tt_sum)
: Tot (LPS.validator (parse_dsum_cases tt_sum parse_tt_cases parse_u32 mk))
= parse_dsum_cases_eq_forall tt_sum parse_tt_cases parse_u32 mk;
  LPS.validate_ext
    (PPS.validate_dsum_cases' tt_sum parse_tt_cases pulse_validate_tt_cases LPI.validate_u32 mk)
    (parse_dsum_cases tt_sum parse_tt_cases parse_u32 mk)

noextract let validate_t (k: kt) : Tot (LPS.validator (parse_t k)) =
  lemma_synth_kt_inj ();
  PPC.validate_synth
    (PPC.validate_compose_context synth_kt_inv (refine_with_tag key_of_tt)
      (parse_dsum_cases tt_sum parse_tt_cases parse_u32)
      validate_dsum_case
      k)
    (synth_t k)

inline_for_extraction noextract
let jump_dsum_case (mk: dsum_key tt_sum)
: Tot (LPS.jumper (parse_dsum_cases tt_sum parse_tt_cases parse_u32 mk))
= parse_dsum_cases_eq_forall tt_sum parse_tt_cases parse_u32 mk;
  LPS.jump_ext
    (PPS.jump_dsum_cases' tt_sum parse_tt_cases pulse_jump_tt_cases LPI.jump_u32 mk)
    (parse_dsum_cases tt_sum parse_tt_cases parse_u32 mk)

noextract let jump_t (k: kt) : Tot (LPS.jumper (parse_t k)) =
  lemma_synth_kt_inj ();
  LPC.jump_synth
    (PPC.jump_compose_context synth_kt_inv (refine_with_tag key_of_tt)
      (parse_dsum_cases tt_sum parse_tt_cases parse_u32)
      jump_dsum_case
      k)
    (synth_t k)

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
