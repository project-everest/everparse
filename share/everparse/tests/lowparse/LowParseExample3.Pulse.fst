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

let vmatch_a (x: U16.t) (v: t) : slprop = pure (x == v.a)
let vmatch_b (x: U32.t) (v: t) : slprop = pure (x == v.b)  
let vmatch_c (x: U16.t) (v: t) : slprop = pure (x == v.c)

(* Accessors via zero_copy_parse composition *)

inline_for_extraction
let access_a : PPB.zero_copy_parse vmatch_a parse_t
= synth_t_injective ();
  PPC.zero_copy_parse_synth
    (PPC.zero_copy_parse_fst #_ #(U16.t & U32.t) #U16.t parse_u16
      (LPC.jump_nondep_then LPI.jump_u16 LPI.jump_u32)
      (PPC.zero_copy_parse_fst #_ #U16.t #U32.t parse_u32 LPI.jump_u16
        (PPB.zero_copy_parse_read leaf_read_u16) ()) ())
    synth_t synth_t_recip

inline_for_extraction
let access_b : PPB.zero_copy_parse vmatch_b parse_t
= synth_t_injective ();
  PPC.zero_copy_parse_synth
    (PPC.zero_copy_parse_fst #_ #(U16.t & U32.t) #U16.t parse_u16
      (LPC.jump_nondep_then LPI.jump_u16 LPI.jump_u32)
      (PPC.zero_copy_parse_snd #_ #U16.t #U32.t LPI.jump_u16
        (PPB.zero_copy_parse_read leaf_read_u32) ()) ())
    synth_t synth_t_recip

inline_for_extraction
let access_c : PPB.zero_copy_parse vmatch_c parse_t
= synth_t_injective ();
  PPC.zero_copy_parse_synth
    (PPC.zero_copy_parse_snd #_ #(U16.t & U32.t) #U16.t
      (LPC.jump_nondep_then LPI.jump_u16 LPI.jump_u32)
      (PPB.zero_copy_parse_read leaf_read_u16) ())
    synth_t synth_t_recip

(* Test function: validate parse_t, then use accessors *)

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
    R.free poffset;
    let input' = PPB.peek_trade_gen parse_t input 0sz off;
    if (U32.eq which 42ul) {
      let x = access_a input';
      with v' pm' . assert (Trade.trade (vmatch_a x v') (PPB.pts_to_parsed parse_t input' #pm' v'));
      Trade.elim (vmatch_a x v') (PPB.pts_to_parsed parse_t input' #pm' v');
      Trade.elim (PPB.pts_to_parsed parse_t input' #pm' v') (S.pts_to input #pm v);
      Cast.uint16_to_uint32 x
    } else if (U32.eq which 1729ul) {
      let x = access_b input';
      with v' pm' . assert (Trade.trade (vmatch_b x v') (PPB.pts_to_parsed parse_t input' #pm' v'));
      Trade.elim (vmatch_b x v') (PPB.pts_to_parsed parse_t input' #pm' v');
      Trade.elim (PPB.pts_to_parsed parse_t input' #pm' v') (S.pts_to input #pm v);
      x
    } else {
      let x = access_c input';
      with v' pm' . assert (Trade.trade (vmatch_c x v') (PPB.pts_to_parsed parse_t input' #pm' v'));
      Trade.elim (vmatch_c x v') (PPB.pts_to_parsed parse_t input' #pm' v');
      Trade.elim (PPB.pts_to_parsed parse_t input' #pm' v') (S.pts_to input #pm v);
      Cast.uint16_to_uint32 x
    }
  } else {
    R.free poffset;
    0ul
  }
}
