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

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
