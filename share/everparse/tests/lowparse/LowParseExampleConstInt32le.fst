module LowParseExampleConstInt32le
#lang-pulse
(* Ported from const int32le test.
   Spec parts are copied from LowParse.Spec.ConstInt32.
   NOTE: Pulse validator for constint32le requires leaf_reader for parse_int32le,
   which is not yet available in the Pulse combinator library.
   The spec is exercised by including the module. *)

include LowParse.Spec.ConstInt32
open Pulse.Lib.Pervasives
open LowParse.Spec.Base

module LPS = LowParse.Pulse.Base
module PPI = LowParse.PulseParse.Int
module I32 = FStar.Int32

(* Pulse jumpers — these don't need a reader *)

inline_for_extraction
let unit_test_constint32le_a_jumper : LPS.jumper (parse_constint32le 5) =
  PPI.jump_constint32le 5

inline_for_extraction
let unit_test_constint32le_b_jumper : LPS.jumper (parse_constint32le 2147483647) =
  PPI.jump_constint32le 2147483647

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
