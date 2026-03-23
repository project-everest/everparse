module LowParseExample3.Pulse
#lang-pulse
include LowParse.Spec.Int
include LowParse.Spec.Combinators
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
module Trade = Pulse.Lib.Trade.Util
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

(* Type definition — mirrors LowParseExample3.Aux *)

type t = { a: U16.t; b: U32.t; c: U16.t; }

let synth_t (xy_z: ((U16.t & U32.t) & U16.t)) : t =
  let ((x, y), z) = xy_z in { a = x; b = y; c = z }

let synth_t_recip (x: t) : ((U16.t & U32.t) & U16.t) = ((x.a, x.b), x.c)

let synth_t_injective () : Lemma (synth_injective synth_t) = ()

let parse_t_base : parser _ ((U16.t & U32.t) & U16.t) =
  parse_u16 `nondep_then` parse_u32 `nondep_then` parse_u16

let parse_t : parser _ t =
  parse_t_base `parse_synth` synth_t

(* Simple leaf_readers for U16 and U32 — PulseParse versions *)

inline_for_extraction
let leaf_read_u16 : PPB.leaf_reader parse_u16 =
  PPB.leaf_reader_of_serialized (LPI.read_u16' ())

inline_for_extraction
let leaf_read_u32 : PPB.leaf_reader parse_u32 =
  PPB.leaf_reader_of_serialized (LPI.read_u32' ())

(* Pulse validator *)

inline_for_extraction
let validate_t : LPS.validator parse_t =
  PPC.validate_synth
    (PPC.validate_nondep_then
      (PPC.validate_nondep_then LPI.validate_u16 LPI.validate_u32)
      LPI.validate_u16)
    synth_t

(* Test function: validate parse_t, then read individual fields
   by re-validating sub-parsers to read them *)

#set-options "--z3rlimit 32"

fn dummy
  (input: S.slice byte)
  (which: U32.t)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  requires S.pts_to input #pm v
  returns res: U32.t
  ensures S.pts_to input #pm v
{
  let poffset = R.alloc 0sz;
  let is_valid = validate_t input poffset;
  if is_valid {
    let off = !poffset;
    parse_synth_eq parse_t_base synth_t (Seq.slice v 0 (Seq.length v));
    nondep_then_eq (nondep_then parse_u16 parse_u32) parse_u16 (Seq.slice v 0 (Seq.length v));
    nondep_then_eq parse_u16 parse_u32 (Seq.slice v 0 (Seq.length v));
    parser_kind_prop_equiv parse_u16_kind parse_u16;
    parser_kind_prop_equiv parse_u32_kind parse_u32;
    if (U32.eq which 42ul) {
      poffset := 0sz;
      let _ = LPI.validate_u16 input poffset;
      let off = !poffset;
      let x = PPB.read_parsed_from_validator_success leaf_read_u16 input 0sz off;
      R.free poffset;
      Cast.uint16_to_uint32 x
    } else if (U32.eq which 1729ul) {
      poffset := 2sz;
      let _ = LPI.validate_u32 input poffset;
      let off = !poffset;
      let x = PPB.read_parsed_from_validator_success leaf_read_u32 input 2sz off;
      R.free poffset;
      x
    } else {
      poffset := 6sz;
      let _ = LPI.validate_u16 input poffset;
      let off = !poffset;
      let x = PPB.read_parsed_from_validator_success leaf_read_u16 input 6sz off;
      R.free poffset;
      Cast.uint16_to_uint32 x
    }
  } else {
    R.free poffset;
    0ul
  }
}
