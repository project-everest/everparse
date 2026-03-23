module LowParseExample9
#lang-pulse
(* Ported from complex dsum test.
   Spec parts are in LowParseExample9.Aux. *)

include LowParseExample9.Aux
open Pulse.Lib.Pervasives

module I32 = FStar.Int32

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
