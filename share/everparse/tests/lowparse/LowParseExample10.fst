module LowParseExample10
#lang-pulse
include LowParseExample10.Aux
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
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
module PPITE = LowParse.PulseParse.IfThenElse
module Trade = Pulse.Lib.Trade.Util
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module I32 = FStar.Int32

(* leaf_reader for parse_u8 *)

inline_for_extraction noextract
let leaf_read_u8 : PPB.leaf_reader parse_u8 =
  PPB.leaf_reader_of_serialized (LPI.read_u8' ())

(* leaf_reader for msg_type = parse_u8 `nondep_then` parse_u8 `nondep_then` parse_u8
   Read the three bytes sequentially using peek_trade_gen *)

inline_for_extraction noextract
let leaf_read_msg_type : PPB.leaf_reader parse_msg_type =
  PPC.leaf_read_nondep_then
    (PPC.leaf_read_nondep_then leaf_read_u8 LPI.jump_u8 leaf_read_u8 ())
    (LPC.jump_nondep_then LPI.jump_u8 LPI.jump_u8)
    leaf_read_u8
    ()

(* Pulse validator *)

inline_for_extraction
let validate_t : LPS.validator parse_t =
  PPITE.validate_ifthenelse parse_t_param
    (PPC.validate_nondep_then (PPC.validate_nondep_then LPI.validate_u8 LPI.validate_u8) LPI.validate_u8)
    leaf_read_msg_type
    (fun b -> if b then LPI.validate_u32 else LPI.validate_u16)
    ()

(* Pulse jumper *)

inline_for_extraction
let jump_msg_type : LPS.jumper parse_msg_type =
  LPC.jump_nondep_then (LPC.jump_nondep_then LPI.jump_u8 LPI.jump_u8) LPI.jump_u8

inline_for_extraction
let jump_t : LPS.jumper parse_t =
  PPITE.jump_ifthenelse parse_t_param
    jump_msg_type
    leaf_read_msg_type
    (fun b -> if b then LPI.jump_u32 else LPI.jump_u16)
    ()

(* leaf_readers for payload types *)

inline_for_extraction noextract
let leaf_read_u16 : PPB.leaf_reader parse_u16 =
  PPB.leaf_reader_of_serialized (LPI.read_u16' ())

inline_for_extraction noextract
let leaf_read_u32 : PPB.leaf_reader parse_u32 =
  PPB.leaf_reader_of_serialized (LPI.read_u32' ())

(* Accessor: read the tag and payload from a validated ifthenelse.
   After validation, use peek_trade_gen to get a sub-slice, read
   the tag to determine which branch, then jump + read payload. *)

#push-options "--z3rlimit 32"

fn access_payload
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased bytes)
  (offset: SZ.t)
  (off: SZ.t)
  (_: squash (LPS.validator_success parse_t offset v off))
  requires pts_to input #pm v
  returns res: t
  ensures pts_to input #pm v
{
  let sinput = Ghost.hide (Seq.slice v (SZ.v offset) (Seq.length v));
  parse_ifthenelse_eq parse_t_param sinput;
  nondep_then_eq (nondep_then parse_u8 parse_u8) parse_u8 sinput;
  nondep_then_eq parse_u8 parse_u8 sinput;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  let tag_off = SZ.add offset 3sz;
  let tag_val = PPB.read_parsed_from_validator_success leaf_read_msg_type input offset tag_off;
  let b = t_tag_cond tag_val;
  Seq.lemma_eq_elim
    (Seq.slice sinput 3 (Seq.length sinput))
    (Seq.slice v (SZ.v tag_off) (Seq.length v));
  if b {
    let payload = PPB.read_parsed_from_validator_success leaf_read_u32 input tag_off off;
    HelloRetryRequest payload
  } else {
    let payload = PPB.read_parsed_from_validator_success leaf_read_u16 input tag_off off;
    Other ({ msg_type = tag_val; contents = payload })
  }
}

#pop-options

(* Separate accessors for HelloRetryRequest and Other payloads,
   using peek_trade_gen to get the payload sub-slice *)

let vmatch_HelloRetryRequest (x: U32.t) (v: t) : slprop =
  pure (v == HelloRetryRequest x)

let vmatch_other (x: U16.t) (v: t) : slprop =
  pure (Other? v /\ x == (match v with Other m -> m.contents | _ -> x))

#push-options "--z3rlimit 32"

inline_for_extraction
fn access_HelloRetryRequest
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  requires PPB.pts_to_parsed parse_t input #pm v ** pure (HelloRetryRequest? v)
  returns res: U32.t
  ensures vmatch_HelloRetryRequest res v **
    Trade.trade (vmatch_HelloRetryRequest res v) (PPB.pts_to_parsed parse_t input #pm v)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (pts_to input #pm w);
  parse_ifthenelse_eq parse_t_param w;
  nondep_then_eq (nondep_then parse_u8 parse_u8) parse_u8 w;
  nondep_then_eq parse_u8 parse_u8 w;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  let off1 = jump_msg_type input 0sz;
  pts_to_len input;
  parser_kind_prop_equiv parse_u32_kind parse_u32;
  let res = PPB.read_parsed_from_validator_success leaf_read_u32 input off1 (len input);
  PPB.pts_to_parsed_intro_injective parse_t input v;
  Trade.trans (PPB.pts_to_parsed parse_t input #pm v) (pts_to input #pm w) (PPB.pts_to_parsed parse_t input #pm v);
  Trade.elim (PPB.pts_to_parsed parse_t input #pm v) (PPB.pts_to_parsed parse_t input #pm v);
  fold (vmatch_HelloRetryRequest res v);
  intro (Trade.trade (vmatch_HelloRetryRequest res v) (PPB.pts_to_parsed parse_t input #pm v))
    #(PPB.pts_to_parsed parse_t input #pm v) fn _ {
    unfold (vmatch_HelloRetryRequest res v)
  };
  res
}

inline_for_extraction
fn access_other
  (input: S.slice byte)
  (#pm: perm)
  (#v: Ghost.erased t)
  requires PPB.pts_to_parsed parse_t input #pm v ** pure (Other? v)
  returns res: U16.t
  ensures vmatch_other res v **
    Trade.trade (vmatch_other res v) (PPB.pts_to_parsed parse_t input #pm v)
{
  PPB.pts_to_parsed_elim input;
  with w . assert (pts_to input #pm w);
  parse_ifthenelse_eq parse_t_param w;
  nondep_then_eq (nondep_then parse_u8 parse_u8) parse_u8 w;
  nondep_then_eq parse_u8 parse_u8 w;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  let off1 = jump_msg_type input 0sz;
  pts_to_len input;
  let res = PPB.read_parsed_from_validator_success leaf_read_u16 input off1 (len input);
  PPB.pts_to_parsed_intro_injective parse_t input v;
  Trade.trans (PPB.pts_to_parsed parse_t input #pm v) (pts_to input #pm w) (PPB.pts_to_parsed parse_t input #pm v);
  Trade.elim (PPB.pts_to_parsed parse_t input #pm v) (PPB.pts_to_parsed parse_t input #pm v);
  fold (vmatch_other res v);
  intro (Trade.trade (vmatch_other res v) (PPB.pts_to_parsed parse_t input #pm v))
    #(PPB.pts_to_parsed parse_t input #pm v) fn _ {
    unfold (vmatch_other res v)
  };
  res
}

#pop-options

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
