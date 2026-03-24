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

(* validate_t and jump_t — same pattern as Low* using dep_enum_destr_tac *)

let validate_t (k: kt) : Tot (LPS.validator (parse_t k)) =
  lemma_synth_kt_inj ();
  PPC.validate_synth
    (PPC.validate_compose_context synth_kt_inv (refine_with_tag key_of_tt)
      (parse_dsum_cases tt_sum parse_tt_cases parse_u32)
      (PPS.validate_dsum_cases tt_sum parse_tt_cases pulse_validate_tt_cases LPI.validate_u32
        (_ by (dep_enum_destr_tac ())))
      k)
    (synth_t k)

let jump_t (k: kt) : Tot (LPS.jumper (parse_t k)) =
  lemma_synth_kt_inj ();
  LPC.jump_synth
    (PPC.jump_compose_context synth_kt_inv (refine_with_tag key_of_tt)
      (parse_dsum_cases tt_sum parse_tt_cases parse_u32)
      (PPS.jump_dsum_cases tt_sum parse_tt_cases pulse_jump_tt_cases LPI.jump_u32
        (_ by (dep_enum_destr_tac ())))
      k)
    (synth_t k)

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
