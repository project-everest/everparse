module LowParseExample8
#lang-pulse
(* Ported from indexed sum test — full Pulse validators and jumpers *)

include LowParseExample8.Aux
open FStar.Tactics.V2
open Pulse.Lib.Pervasives open Pulse.Lib.Slice.Util open Pulse.Lib.Trade
open Pulse.Lib.Slice
open LowParse.Spec.Base

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module LPI = LowParse.Pulse.Int
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module PPS = LowParse.PulseParse.Sum
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module I32 = FStar.Int32

(* Pulse validators for each case *)

inline_for_extraction noextract
let pulse_validate_cases (x: sum_key t_sum) : Tot (LPS.validator (dsnd (parse_cases x))) = match x with
  | Ka -> (LPI.validate_u8 <: LPS.validator (dsnd (parse_cases x)))
  | Kb -> (LPI.validate_u16 <: LPS.validator (dsnd (parse_cases x)))

let validate_t (k: k_t) : Tot (LPS.validator (parse_t k)) =
  [@inline_let] let _ = assert (k == case_as_case_enum k) in
  [@inline_let] let k : sum_key t_sum = k in
  PPS.validate_sum_cases t_sum parse_cases pulse_validate_cases (_ by (dep_enum_destr_tac ())) k

(* Pulse jumpers for each case *)

inline_for_extraction noextract
let pulse_jump_cases (x: sum_key t_sum) : Tot (LPS.jumper (dsnd (parse_cases x))) = match x with
  | Ka -> (LPI.jump_u8 <: LPS.jumper (dsnd (parse_cases x)))
  | Kb -> (LPI.jump_u16 <: LPS.jumper (dsnd (parse_cases x)))

let jump_t (k: k_t) : Tot (LPS.jumper (parse_t k)) =
  [@inline_let] let _ = assert (k == case_as_case_enum k) in
  [@inline_let] let k : sum_key t_sum = k in
  PPS.jump_sum_cases t_sum parse_cases pulse_jump_cases (_ by (dep_enum_destr_tac ())) k

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
