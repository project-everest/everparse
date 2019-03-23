module LowParse.Spec.Int
include LowParse.Spec.Base

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

inline_for_extraction
let parse_u8_kind : parser_kind = total_constant_size_parser_kind 1

val parse_u8: parser parse_u8_kind U8.t

val parse_u8_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 1))
  (ensures (
    let pp = parse parse_u8 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U8.v v == E.be_to_n (Seq.slice b 0 1)
  )))

val parse_u8_spec'
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 1))
  (ensures (
    let pp = parse parse_u8 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    v == Seq.index b 0
  )))

val serialize_u8 : serializer parse_u8

val serialize_u8_spec
  (x: U8.t)
: Lemma
  (serialize serialize_u8 x `Seq.equal` Seq.create 1 x)

inline_for_extraction
let parse_u16_kind : parser_kind =
  total_constant_size_parser_kind 2

val parse_u16: parser parse_u16_kind U16.t

val parse_u16_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 2))
  (ensures (
    let pp = parse parse_u16 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U16.v v == E.be_to_n (Seq.slice b 0 2)
  )))

val serialize_u16 : serializer parse_u16

inline_for_extraction
let parse_u32_kind : parser_kind =
  total_constant_size_parser_kind 4

val parse_u32: parser parse_u32_kind U32.t

val parse_u32_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 4))
  (ensures (
    let pp = parse parse_u32 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U32.v v == E.be_to_n (Seq.slice b 0 4)
  )))

val serialize_u32 : serializer parse_u32
