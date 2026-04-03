module LowParseExample7
#lang-pulse
(* TLS ClientHello spec test — pure spec, no Low*.
   Ported from tests/lowparse/LowParseExample7.fst *)

open Pulse.Lib.Pervasives

module Aux = LowParseExample7.Aux
module I32 = FStar.Int32

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
