module LowParse.Spec.Int
include LowParse.Spec.Base

module Seq = FStar.Seq
module E = FStar.Endianness
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

inline_for_extraction
let parse_u8_kind : parser_kind = total_constant_size_parser_kind 1

val tot_parse_u8: tot_parser parse_u8_kind U8.t

let parse_u8: parser parse_u8_kind U8.t = tot_parse_u8

val parse_u8_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 1))
  (ensures (
    let pp = parse parse_u8 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U8.v v == E.be_to_n (Seq.slice b 0 1) /\ consumed == 1
  )))

val parse_u8_spec'
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 1))
  (ensures (
    let pp = parse parse_u8 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    v == Seq.index b 0 /\ consumed == 1
  )))

val tot_serialize_u8 : tot_serializer #parse_u8_kind tot_parse_u8

let serialize_u8 : serializer parse_u8 = tot_serialize_u8

val serialize_u8_spec
  (x: U8.t)
: Lemma
  (serialize serialize_u8 x `Seq.equal` Seq.create 1 x)

let serialize_u8_spec'
  (x: U8.t)
: Lemma
  (let s = serialize serialize_u8 x in
    Seq.length s == 1 /\
    Seq.index s 0 == x)
= serialize_u8_spec x

let serialize_u8_spec_be
  (x: U8.t)
: Lemma
  (serialize serialize_u8 x == E.n_to_be 1 (U8.v x))
= let s = E.n_to_be 1 (U8.v x) in
  Seq.slice_length s;
  parse_u8_spec s;
  parse_injective parse_u8 (serialize serialize_u8 x) s

inline_for_extraction
let parse_u16_kind : parser_kind =
  total_constant_size_parser_kind 2

val tot_parse_u16 : tot_parser parse_u16_kind U16.t

let parse_u16: parser parse_u16_kind U16.t = tot_parse_u16

val parse_u16_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 2))
  (ensures (
    let pp = parse parse_u16 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U16.v v == E.be_to_n (Seq.slice b 0 2) /\ consumed == 2
  )))

val tot_serialize_u16 : tot_serializer #parse_u16_kind tot_parse_u16

let serialize_u16 : serializer parse_u16 = tot_serialize_u16

let serialize_u16_spec_be
  (x: U16.t)
: Lemma
  (serialize serialize_u16 x == E.n_to_be 2 (U16.v x))
= let s = E.n_to_be 2 (U16.v x) in
  Seq.slice_length s;
  parse_u16_spec s;
  parse_injective parse_u16 (serialize serialize_u16 x) s

inline_for_extraction
let parse_u32_kind : parser_kind =
  total_constant_size_parser_kind 4

val tot_parse_u32: tot_parser parse_u32_kind U32.t

let parse_u32: parser parse_u32_kind U32.t = tot_parse_u32

val parse_u32_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 4))
  (ensures (
    let pp = parse parse_u32 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U32.v v == E.be_to_n (Seq.slice b 0 4) /\ consumed == 4
  )))

val tot_serialize_u32 : tot_serializer #parse_u32_kind tot_parse_u32

let serialize_u32 : serializer parse_u32 = tot_serialize_u32

let serialize_u32_spec_be
  (x: U32.t)
: Lemma
  (serialize serialize_u32 x == E.n_to_be 4 (U32.v x))
= let s = E.n_to_be 4 (U32.v x) in
  Seq.slice_length s;
  parse_u32_spec s;
  parse_injective parse_u32 (serialize serialize_u32 x) s

inline_for_extraction
let parse_u64_kind : parser_kind =
  total_constant_size_parser_kind 8

val tot_parse_u64: tot_parser parse_u64_kind U64.t

let parse_u64: parser parse_u64_kind U64.t = tot_parse_u64

val parse_u64_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 8))
  (ensures (
    let pp = parse parse_u64 b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U64.v v == E.be_to_n (Seq.slice b 0 8) /\ consumed == 8
  )))

val tot_serialize_u64 : tot_serializer #parse_u64_kind tot_parse_u64

let serialize_u64 : serializer parse_u64 = tot_serialize_u64

let serialize_u64_spec_be
  (x: U64.t)
: Lemma
  (serialize serialize_u64 x == E.n_to_be 8 (U64.v x))
= let s = E.n_to_be 8 (U64.v x) in
  Seq.slice_length s;
  parse_u64_spec s;
  parse_injective parse_u64 (serialize serialize_u64 x) s

val parse_u64_le: parser parse_u64_kind U64.t

val parse_u64_le_spec
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 8))
  (ensures (
    let pp = parse parse_u64_le b in
    Some? pp /\ (
    let (Some (v, consumed)) = pp in
    U64.v v == E.le_to_n (Seq.slice b 0 8) /\ consumed == 8
  )))

val serialize_u64_le : serializer parse_u64_le
