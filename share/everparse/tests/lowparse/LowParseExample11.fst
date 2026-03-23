module LowParseExample11
#lang-pulse
(* Ported from vclist test.
   Original used parse_vclist with BCVLI encoding.
   We keep spec parts (parser, serializer).
   NOTE: Pulse validators for VCList require leaf_reader for parse_bcvli
   (bounded_integer_le readers), which are not yet available.
   The spec is fully verified. *)

include LowParse.Spec.VCList
include LowParse.Spec.BCVLI
include LowParse.Spec.Int
open Pulse.Lib.Pervasives
open LowParse.Spec.Base

module U32 = FStar.UInt32
module L = FStar.List.Tot
module I32 = FStar.Int32

type elem = U32.t

type t = (l: list elem { let ln = L.length l in 10 <= ln /\ ln <= 1000 })

inline_for_extraction
let parse_t_kind : parser_kind = strong_parser_kind 11 5005 None

let parse_t' = parse_vclist 10 1000 parse_bcvli parse_bcvli

let kind_eq : squash (get_parser_kind parse_t' == parse_t_kind) =
  _ by (FStar.Tactics.trefl ())

let type_eq : squash (t == vlarray elem 10 1000) = _ by (FStar.Tactics.trefl ())

let parse_t : parser parse_t_kind t = parse_t'

let serialize_t : serializer parse_t = serialize_vclist 10 1000 serialize_bcvli serialize_bcvli

fn main ()
  requires emp
  returns r: I32.t
  ensures emp
{ 0l }
