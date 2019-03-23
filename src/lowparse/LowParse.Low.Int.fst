module LowParse.Low.Int
open LowParse.Low.Combinators

module Aux = LowParse.Low.Int.Aux
module Unique = LowParse.Spec.Int.Unique
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer

inline_for_extraction
let read_u8 =
  leaf_reader_ext Aux.read_u8 parse_u8 (fun x -> Unique.parse_u8_unique x)

inline_for_extraction
let read_u16 =
  leaf_reader_ext Aux.read_u16 parse_u16 (fun x -> Unique.parse_u16_unique x)

inline_for_extraction
let read_u32 =
  leaf_reader_ext Aux.read_u32 parse_u32 (fun x -> Unique.parse_u32_unique x)

inline_for_extraction
let serialize32_u8 : serializer32 serialize_u8 = fun v b ->
  [@inline_let] let _ = Unique.serialize_u8_unique v in
  Aux.serialize32_u8 v b

inline_for_extraction
let serialize32_u16 : serializer32 serialize_u16 = fun v b ->
  [@inline_let] let _ = Unique.serialize_u16_unique v in
  Aux.serialize32_u16 v b

inline_for_extraction
let serialize32_u32 : serializer32 serialize_u32 = fun v b ->
  [@inline_let] let _ = Unique.serialize_u32_unique v in
  Aux.serialize32_u32 v b

let write_u8 = leaf_writer_strong_of_serializer32 serialize32_u8 ()

let write_u16 = leaf_writer_strong_of_serializer32 serialize32_u16 ()

let write_u32 = leaf_writer_strong_of_serializer32 serialize32_u32 ()
