module LowParseExample12
#lang-pulse
(* Ported from vlgen + DER test.
   Original used parse_vlgen with DER length encoding.
   We keep spec parts (parser, serializer).
   NOTE: Pulse validators for VLGen require leaf_reader for bounded_integer
   and DER length types, which are not yet available in the Pulse combinator library.
   The spec is fully verified. *)

include LowParse.Spec.VLGen
include LowParse.Spec.Bytes
include LowParse.Spec.DER
open Pulse.Lib.Pervasives
open LowParse.Spec.Base

module I32 = FStar.Int32

inline_for_extraction
type t = parse_bounded_vlbytes_t 0 512

inline_for_extraction
let parse_t_kind : parser_kind = strong_parser_kind 3 517 None

let parse_t' = parse_vlgen 0 1023 (parse_bounded_der_length32 0 1023) (serialize_bounded_vlbytes 0 512)

let kind_eq : squash (parse_t_kind == get_parser_kind parse_t') = _ by (FStar.Tactics.trefl ())

let parse_t : parser parse_t_kind t = parse_t'

let serialize_t : serializer parse_t = serialize_vlgen 0 1023 (serialize_bounded_der_length32 0 1023) (serialize_bounded_vlbytes 0 512)

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
