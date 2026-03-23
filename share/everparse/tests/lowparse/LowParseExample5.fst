module LowParseExample5
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
module I32 = FStar.Int32

(* Type definitions — from LowParseExample5.Aux *)

noeq
type inner = {
  left: U16.t;
  right: U16.t;
}

noeq
type t = {
  inner: inner;
  last: U32.t;
}

(* Synth functions for inner *)

let synth_inner (x: (U16.t & U16.t)) : Tot inner =
  let (left, right) = x in { left = left; right = right; }

let synth_inner_recip (x: inner) : Tot (U16.t & U16.t) =
  (x.left, x.right)

let synth_inner_injective () : Lemma (synth_injective synth_inner) = ()

(* Parser for inner *)

let parse_inner_raw : parser _ (U16.t & U16.t) =
  parse_u16 `nondep_then` parse_u16

let parse_inner : parser _ inner =
  parse_inner_raw `parse_synth` synth_inner

(* Synth functions for t *)

let synth_t (x: (inner & U32.t)) : Tot t =
  let (i, l) = x in { inner = i; last = l; }

let synth_t_recip (x: t) : Tot (inner & U32.t) =
  (x.inner, x.last)

let synth_t_injective () : Lemma (synth_injective synth_t) = ()

(* Parser for t *)

let parse_t_raw : parser _ (inner & U32.t) =
  parse_inner `nondep_then` parse_u32

let parse_t : parser _ t =
  parse_t_raw `parse_synth` synth_t

(* Pulse validators *)

inline_for_extraction
let validate_inner : LPS.validator parse_inner =
  PPC.validate_synth
    (PPC.validate_nondep_then LPI.validate_u16 LPI.validate_u16)
    synth_inner

inline_for_extraction
let validate_t : LPS.validator parse_t =
  PPC.validate_synth
    (PPC.validate_nondep_then validate_inner LPI.validate_u32)
    synth_t

(* Pulse jumpers *)

inline_for_extraction
let jump_inner : LPS.jumper parse_inner =
  LPC.jump_synth
    (LPC.jump_nondep_then LPI.jump_u16 LPI.jump_u16)
    synth_inner

inline_for_extraction
let jump_t : LPS.jumper parse_t =
  LPC.jump_synth
    (LPC.jump_nondep_then jump_inner LPI.jump_u32)
    synth_t

(* Leaf readers *)

inline_for_extraction
let leaf_read_u16 : PPB.leaf_reader parse_u16 =
  PPB.leaf_reader_of_serialized (LPI.read_u16' ())

inline_for_extraction
let leaf_read_u32 : PPB.leaf_reader parse_u32 =
  PPB.leaf_reader_of_serialized (LPI.read_u32' ())

(* vmatch predicates *)

let vmatch_left (x: U16.t) (v: t) : slprop = pure (x == v.inner.left)
let vmatch_right (x: U16.t) (v: t) : slprop = pure (x == v.inner.right)
let vmatch_last (x: U32.t) (v: t) : slprop = pure (x == v.last)

(* Accessors via zero_copy_parse composition *)

inline_for_extraction
let access_left : PPB.zero_copy_parse vmatch_left parse_t
= synth_t_injective ();
  synth_inner_injective ();
  PPC.zero_copy_parse_synth
    (PPC.zero_copy_parse_fst #_ #inner #U32.t parse_u32
      jump_inner
      (PPC.zero_copy_parse_synth
        (PPC.zero_copy_parse_fst #_ #U16.t #U16.t parse_u16 LPI.jump_u16
          (PPB.zero_copy_parse_read leaf_read_u16) ())
        synth_inner synth_inner_recip) ())
    synth_t synth_t_recip

inline_for_extraction
let access_right : PPB.zero_copy_parse vmatch_right parse_t
= synth_t_injective ();
  synth_inner_injective ();
  PPC.zero_copy_parse_synth
    (PPC.zero_copy_parse_fst #_ #inner #U32.t parse_u32
      jump_inner
      (PPC.zero_copy_parse_synth
        (PPC.zero_copy_parse_snd #_ #U16.t #U16.t LPI.jump_u16
          (PPB.zero_copy_parse_read leaf_read_u16) ())
        synth_inner synth_inner_recip) ())
    synth_t synth_t_recip

inline_for_extraction
let access_last : PPB.zero_copy_parse vmatch_last parse_t
= synth_t_injective ();
  PPC.zero_copy_parse_synth
    (PPC.zero_copy_parse_snd #_ #inner #U32.t
      jump_inner
      (PPB.zero_copy_parse_read leaf_read_u32) ())
    synth_t synth_t_recip

(* Test function *)

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
    if (U32.eq which 42ul) {
      let x = access_left input';
      with v' pm' . assert (Trade.trade (vmatch_left x v') (PPB.pts_to_parsed parse_t input' #pm' v'));
      Trade.elim (vmatch_left x v') (PPB.pts_to_parsed parse_t input' #pm' v');
      Trade.elim (PPB.pts_to_parsed parse_t input' #pm' v') (S.pts_to input #pm v);
      FStar.Int.Cast.uint16_to_uint32 x
    } else if (U32.eq which 1729ul) {
      let x = access_last input';
      with v' pm' . assert (Trade.trade (vmatch_last x v') (PPB.pts_to_parsed parse_t input' #pm' v'));
      Trade.elim (vmatch_last x v') (PPB.pts_to_parsed parse_t input' #pm' v');
      Trade.elim (PPB.pts_to_parsed parse_t input' #pm' v') (S.pts_to input #pm v);
      x
    } else {
      let x = access_right input';
      with v' pm' . assert (Trade.trade (vmatch_right x v') (PPB.pts_to_parsed parse_t input' #pm' v'));
      Trade.elim (vmatch_right x v') (PPB.pts_to_parsed parse_t input' #pm' v');
      Trade.elim (PPB.pts_to_parsed parse_t input' #pm' v') (S.pts_to input #pm v);
      FStar.Int.Cast.uint16_to_uint32 x
    }
  } else {
    0ul
  }
}

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
