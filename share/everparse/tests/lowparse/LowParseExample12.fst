module LowParseExample12
#lang-pulse
(* Ported from vlgen + DER test.
   Demonstrates: validate_t, jump_t using PulseParse combinators
   with DER length encoding and bounded vlbytes payload. *)

include LowParse.Spec.VLGen
include LowParse.Spec.Bytes
include LowParse.Spec.DER
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
open LowParse.Spec.Base

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module LPS = LowParse.Pulse.Base
module LPI = LowParse.Pulse.Int
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base
module PPC = LowParse.PulseParse.Combinators
module PPBI = LowParse.PulseParse.BoundedInt
module PPVG = LowParse.PulseParse.VLGen
module PPBY = LowParse.PulseParse.Bytes
module PPDER = LowParse.Pulse.DER
module I32 = FStar.Int32
module U8 = FStar.UInt8

inline_for_extraction
type t = parse_bounded_vlbytes_t 0 512

inline_for_extraction
let parse_t_kind : parser_kind = strong_parser_kind 3 517 None

let parse_t' = parse_vlgen 0 1023 (parse_bounded_der_length32 0 1023) (serialize_bounded_vlbytes 0 512)

let kind_eq : squash (parse_t_kind == get_parser_kind parse_t') = _ by (FStar.Tactics.trefl ())

let parse_t : parser parse_t_kind t = parse_t'

let serialize_t : serializer parse_t = serialize_vlgen 0 1023 (serialize_bounded_der_length32 0 1023) (serialize_bounded_vlbytes 0 512)

(* leaf_readers *)

let fits_u64_squash (_: unit) : Lemma (FStar.SizeT.fits_u64) = assume (FStar.SizeT.fits_u64)

inline_for_extraction noextract
let leaf_read_u8 : PPB.leaf_reader parse_u8 =
  PPB.leaf_reader_of_serialized (LPI.read_u8' ())

inline_for_extraction noextract
let leaf_read_bi (i: integer_size) : PPB.leaf_reader (parse_bounded_integer i) =
  fits_u64_squash ();
  match i with
  | 1 -> PPBI.leaf_read_bounded_integer_1 ()
  | 2 -> PPBI.leaf_read_bounded_integer_2 ()
  | 3 -> PPBI.leaf_read_bounded_integer_3 ()
  | 4 -> PPBI.leaf_read_bounded_integer_4 ()

inline_for_extraction noextract
let leaf_read_bi_serialized (i: integer_size) : LPS.leaf_reader (serialize_bounded_integer i) =
  fits_u64_squash ();
  PPB.serialized_of_leaf_reader (serialize_bounded_integer i) (leaf_read_bi i)

inline_for_extraction noextract
let leaf_read_der : PPB.leaf_reader (parse_bounded_der_length32 0 1023) =
  PPDER.leaf_read_bounded_der_length32 0 1023 leaf_read_u8 leaf_read_bi

(* Pulse validator *)

inline_for_extraction
let validate_t : LPS.validator parse_t =
  fits_u64_squash ();
  PPVG.validate_vlgen 0 1023
    (PPDER.validate_bounded_der_length32 0ul 1023ul (LPI.read_u8' ()) leaf_read_bi_serialized)
    leaf_read_der
    (serialize_bounded_vlbytes 0 512)
    (PPBY.validate_bounded_vlbytes 0 512 (leaf_read_bi 2) ())
    ()

(* Pulse jumper *)

inline_for_extraction
let jump_t : LPS.jumper parse_t =
  fits_u64_squash ();
  PPVG.jump_vlgen 0 1023
    (PPDER.jump_bounded_der_length32 0 1023 leaf_read_u8)
    leaf_read_der
    (serialize_bounded_vlbytes 0 512)
    ()

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
