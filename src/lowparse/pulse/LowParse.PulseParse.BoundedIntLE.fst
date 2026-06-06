module LowParse.PulseParse.BoundedIntLE
#lang-pulse
include LowParse.Spec.BoundedInt
open Pulse.Lib.Pervasives
open LowParse.Spec.Combinators

module PPB = LowParse.PulseParse.Base
module PPBI = LowParse.PulseParse.BoundedInt
module PPC = LowParse.PulseParse.Combinators
module Cast = FStar.Int.Cast
module U32 = FStar.UInt32

let parse_u16_le_unfold
: squash (parse_u16_le == parse_synth (parse_bounded_integer_le 2) synth_u16_le)
= ()

inline_for_extraction
let read_u16_le : PPB.leaf_reader parse_u16_le =
  [@@inline_let] let _ = synth_u16_le_injective in
  [@@inline_let] let _ = synth_u16_le_inverse in
  [@@inline_let] let _ = parse_u16_le_unfold in
  PPC.leaf_read_synth PPBI.leaf_read_bounded_integer_le_2 synth_u16_le synth_u16_le_recip (fun x -> Cast.uint32_to_uint16 x)

inline_for_extraction
let read_u32_le : PPB.leaf_reader parse_u32_le =
  [@@inline_let] let _ = assert_norm (parse_u32_le == parse_synth (parse_bounded_integer_le 4) synth_u32_le) in
  PPC.leaf_read_synth #(bounded_integer 4) #U32.t #(parse_bounded_integer_kind 4) #(parse_bounded_integer_le 4)
    PPBI.leaf_read_bounded_integer_le_4 synth_u32_le synth_u32_le_recip (fun x -> (x <: U32.t))
