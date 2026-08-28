module LowParse.Pulse.ArrayPtr.IntLE
friend LowParse.Spec.BoundedInt
#lang-pulse

open Pulse.Lib.Pervasives
open LowParse.Spec.Base
open LowParse.Spec.BoundedInt
open LowParse.Spec.Combinators

module U8 = FStar.UInt8
module E = LowParse.Endianness
module AP = Pulse.Lib.ArrayPtr
module API = LowParse.Pulse.ArrayPtr.Int

(* LowParse.Spec.BoundedInt states this for synth_u16_le but not for
   synth_u32_le, which is the identity. *)
let synth_u32_le_injective : squash (synth_injective synth_u32_le) = ()

inline_for_extraction
noextract
fn read_u16_le' (_: unit) : API.leaf_reader parse_u16_le
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  API.parse_constant_size_eq parse_u16_le v;
  synth_u16_le_injective;
  parse_synth_eq (parse_bounded_integer_le 2) synth_u16_le v;
  parse_bounded_integer_le_eq 2 v;
  E.lemma_le_to_n_is_bounded (Seq.slice v 0 2);
  API.le_to_n_2 x 0sz
}

let read_u16_le = read_u16_le' ()

inline_for_extraction
noextract
fn read_u32_le' (_: unit) : API.leaf_reader parse_u32_le
= (x: AP.ptr U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
{
  API.parse_constant_size_eq parse_u32_le v;
  synth_u32_le_injective;
  parse_synth_eq (parse_bounded_integer_le 4) synth_u32_le v;
  parse_bounded_integer_le_eq 4 v;
  E.lemma_le_to_n_is_bounded (Seq.slice v 0 4);
  API.le_to_n_4 x 0sz
}

let read_u32_le = read_u32_le' ()
