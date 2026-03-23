module LowParseExample10
#lang-pulse
(* Ported from ifthenelse test.
   Spec parts are in LowParseExample10.Aux.
   NOTE: Pulse validator for ifthenelse requires a leaf_reader for
   parse_flbytes 3, which is not yet available in the Pulse combinator library.
   The spec (parser, serializer) is fully verified. *)

include LowParseExample10.Aux
open Pulse.Lib.Pervasives

module I32 = FStar.Int32

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
