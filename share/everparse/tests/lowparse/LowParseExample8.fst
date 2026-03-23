module LowParseExample8
#lang-pulse
(* Ported from indexed sum test.
   Spec parts are in LowParseExample8.Aux.
   Pulse validators are defined here. *)

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
module U32 = FStar.UInt32
module I32 = FStar.Int32

(* Pulse validators for each case *)

inline_for_extraction
let pulse_validate_cases (x: sum_key t_sum) : Tot (LPS.validator (dsnd (parse_cases x))) = match x with
  | Ka -> (LPI.validate_u8 <: LPS.validator (dsnd (parse_cases x)))
  | Kb -> (LPI.validate_u16 <: LPS.validator (dsnd (parse_cases x)))

inline_for_extraction
let pulse_jump_cases (x: sum_key t_sum) : Tot (LPS.jumper (dsnd (parse_cases x))) = match x with
  | Ka -> (LPI.jump_u8 <: LPS.jumper (dsnd (parse_cases x)))
  | Kb -> (LPI.jump_u16 <: LPS.jumper (dsnd (parse_cases x)))

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
