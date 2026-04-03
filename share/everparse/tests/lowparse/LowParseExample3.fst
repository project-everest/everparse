module LowParseExample3
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

unfold let parse_t_base : parser _ ((U16.t & U32.t) & U16.t) =
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
  LPC.validate_synth
    (PPC.validate_nondep_then
      (PPC.validate_nondep_then LPI.validate_u16 LPI.validate_u32)
      LPI.validate_u16)
    synth_t

(* clens definitions for accessor-based field access *)

include LowParse.CLens

let clens_a : clens t U16.t = {
  clens_cond = (fun _ -> True);
  clens_get = (fun x -> x.a);
}

let clens_b : clens t U32.t = {
  clens_cond = (fun _ -> True);
  clens_get = (fun x -> x.b);
}

let clens_c : clens t U16.t = {
  clens_cond = (fun _ -> True);
  clens_get = (fun x -> x.c);
}

(* Accessors using combinator composition — mirrors Low* pattern:
   accessor_synth_inv (unwrap synth) → accessor_fst/snd (navigate pairs) → accessor_ext (relabel clens) *)

let access_a : PPB.accessor parse_t parse_u16 clens_a =
  PPC.accessor_ext
    (PPC.accessor_then_fst
      (PPC.accessor_then_fst
        (PPC.accessor_synth_inv synth_t synth_t_recip)
        (LPC.jump_nondep_then LPI.jump_u16 LPI.jump_u32) () ())
      LPI.jump_u16 () ())
    clens_a ()

let access_b : PPB.accessor parse_t parse_u32 clens_b =
  PPC.accessor_ext
    (PPC.accessor_then_snd
      (PPC.accessor_then_fst
        (PPC.accessor_synth_inv synth_t synth_t_recip)
        (LPC.jump_nondep_then LPI.jump_u16 LPI.jump_u32) () ())
      LPI.jump_u16 () ())
    clens_b ()

let access_c : PPB.accessor parse_t parse_u16 clens_c =
  PPC.accessor_ext
    (PPC.accessor_then_snd
      (PPC.accessor_synth_inv synth_t synth_t_recip)
      (LPC.jump_nondep_then LPI.jump_u16 LPI.jump_u32) () ())
    clens_c ()

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
  let mut poffset = 0sz;
  let is_valid = validate_t input poffset;
  if is_valid {
    let off = !poffset;
    let input' = PPB.peek_trade_gen parse_t input 0sz off;
    with v1 . assert (PPB.pts_to_parsed parse_t input' #(pm /. 2.0R) v1);
    if (U32.eq which 42ul) {
      let sub = access_a input';
      with v2 pm2 . assert (PPB.pts_to_parsed parse_u16 sub #pm2 v2);
      let x = leaf_read_u16 sub;
      Trade.elim (PPB.pts_to_parsed parse_u16 sub #pm2 v2) (PPB.pts_to_parsed parse_t input' #(pm /. 2.0R) v1);
      Trade.elim (PPB.pts_to_parsed parse_t input' #(pm /. 2.0R) v1) (S.pts_to input #pm v);
      Cast.uint16_to_uint32 x
    } else if (U32.eq which 1729ul) {
      let sub = access_b input';
      with v2 pm2 . assert (PPB.pts_to_parsed parse_u32 sub #pm2 v2);
      let x = leaf_read_u32 sub;
      Trade.elim (PPB.pts_to_parsed parse_u32 sub #pm2 v2) (PPB.pts_to_parsed parse_t input' #(pm /. 2.0R) v1);
      Trade.elim (PPB.pts_to_parsed parse_t input' #(pm /. 2.0R) v1) (S.pts_to input #pm v);
      x
    } else {
      let sub = access_c input';
      with v2 pm2 . assert (PPB.pts_to_parsed parse_u16 sub #pm2 v2);
      let x = leaf_read_u16 sub;
      Trade.elim (PPB.pts_to_parsed parse_u16 sub #pm2 v2) (PPB.pts_to_parsed parse_t input' #(pm /. 2.0R) v1);
      Trade.elim (PPB.pts_to_parsed parse_t input' #(pm /. 2.0R) v1) (S.pts_to input #pm v);
      Cast.uint16_to_uint32 x
    }
  } else {
    0ul
  }
}

(* Test function: create a byte array, convert to slice, call dummy *)

module A = Pulse.Lib.Array

fn test ()
  requires emp
  ensures emp
{
  let mut arr = [| 0uy ; 8sz |];
  let input = S.from_array arr 8sz;
  input.(0sz) <- 0x01uy;
  input.(1sz) <- 0x02uy;
  input.(2sz) <- 0x55uy;
  input.(3sz) <- 0xAAuy;
  input.(4sz) <- 0x34uy;
  input.(5sz) <- 0x45uy;
  input.(6sz) <- 0xBAuy;
  input.(7sz) <- 0xABuy;
  let res = dummy input 42ul;
  S.to_array input;
  ()
}

module I32 = FStar.Int32

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{
  test ();
  0l
}
