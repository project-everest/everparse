module LowParseExample9
#lang-pulse
include LowParseExample9.Aux
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module LPI = LowParse.Pulse.Int
module LPC = LowParse.Pulse.Combinators
module PPC = LowParse.PulseParse.Combinators
module PPS = LowParse.PulseParse.Sum
module I32 = FStar.Int32

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

(* Pre-compute tactic-generated destructors *)

inline_for_extraction noextract
let tt_validate_destr : dep_maybe_enum_destr_t (dsum_enum tt_sum) (PPS.validate_dsum_cases_t tt_sum parse_tt_cases parse_u32)
= _ by (dep_maybe_enum_destr_t_tac ())

inline_for_extraction noextract
let tt_jump_destr : dep_maybe_enum_destr_t (dsum_enum tt_sum) (PPS.jump_dsum_cases_t tt_sum parse_tt_cases parse_u32)
= _ by (dep_maybe_enum_destr_t_tac ())

(* validate_t and jump_t using generic PPS.validate_dsum_cases_fn *)

#push-options "--z3rlimit 32"

inline_for_extraction
fn validate_t (k: kt) : LPS.validator (parse_t k)
=
  (input: S.slice byte) (poffset: R.ref SZ.t)
  (#offset: Ghost.erased SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  lemma_synth_kt_inj ();
  parse_t_eq k (Seq.slice v (SZ.v offset) (Seq.length v));
  PPS.validate_dsum_cases_fn tt_sum parse_tt_cases pulse_validate_tt_cases LPI.validate_u32
    tt_validate_destr (synth_kt_inv k) input poffset
}

inline_for_extraction
fn jump_t (k: kt) : LPS.jumper (parse_t k)
=
  (input: S.slice byte) (offset: SZ.t) (#pm: perm) (#v: Ghost.erased bytes)
{
  lemma_synth_kt_inj ();
  parse_t_eq k (Seq.slice v (SZ.v offset) (Seq.length v));
  PPS.jump_dsum_cases_fn tt_sum parse_tt_cases pulse_jump_tt_cases LPI.jump_u32
    tt_jump_destr (synth_kt_inv k) input offset
}

#pop-options

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
