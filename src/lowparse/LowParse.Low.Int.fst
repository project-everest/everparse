module LowParse.Low.Int
open LowParse.Low.Combinators

module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module E = FStar.Endianness
module LE = LowParse.Low.Endianness

friend LowParse.Spec.Int

let read_u8 : leaf_reader parse_u8 =
  decode_u8_injective ();
  make_total_constant_size_reader 1 1ul
    decode_u8
    ()
    (fun #rrel #rel b pos -> B.index b pos)

inline_for_extraction
let read_u16 =
  decode_u16_injective ();
  make_total_constant_size_reader 2 2ul
    #U16.t
    decode_u16
    ()
    (fun #rrel #rel sl pos ->
      LE.load16_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) sl pos)

inline_for_extraction
let read_u32 =
  decode_u32_injective ();
  make_total_constant_size_reader 4 4ul
    #U32.t
    decode_u32
    ()
    (fun #rrel #rel sl pos ->
      LE.load32_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) sl pos)

inline_for_extraction
let read_u64 =
  decode_u64_injective ();
  make_total_constant_size_reader 8 8ul
    #U64.t
    decode_u64
    ()
    (fun #rrel #rel sl pos ->
      LE.load64_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) sl pos)

inline_for_extraction
let read_u64_le =
  decode_u64_le_injective ();
  make_total_constant_size_reader 8 8ul
    #U64.t
    decode_u64_le
    ()
    (fun #rrel #rel sl pos ->
      LE.load64_le_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) sl pos)

inline_for_extraction
let serialize32_u8 : serializer32 serialize_u8 = fun v #rrel #rel b pos ->
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 1)) pos v;
  1ul

inline_for_extraction
let serialize32_u16 : serializer32 serialize_u16 = fun v #rrel #rel b pos ->
  let h = HST.get () in
  LE.writable_store_pre b (U32.v pos) 2 (fun s -> E.be_to_n s == U16.v v) h;
  LE.store16_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) b pos v;
  let h' = HST.get () in
  LE.store_post_modifies b (U32.v pos) 2 (fun s -> E.be_to_n s == U16.v v) h h';
  2ul

inline_for_extraction
let serialize32_u32 : serializer32 serialize_u32 = fun v #rrel #rel b pos ->
  let h = HST.get () in
  LE.writable_store_pre b (U32.v pos) 4 (fun s -> E.be_to_n s == U32.v v) h;
  LE.store32_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) b pos v;
  let h' = HST.get () in
  LE.store_post_modifies b (U32.v pos) 4 (fun s -> E.be_to_n s == U32.v v) h h';
  4ul

inline_for_extraction
let serialize32_u64 : serializer32 serialize_u64 = fun v #rrel #rel b pos ->
  let h = HST.get () in
  LE.writable_store_pre b (U32.v pos) 8 (fun s -> E.be_to_n s == U64.v v) h;
  LE.store64_be_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) b pos v;
  let h' = HST.get () in
  LE.store_post_modifies b (U32.v pos) 8 (fun s -> E.be_to_n s == U64.v v) h h';
  8ul

inline_for_extraction
let serialize32_u64_le : serializer32 serialize_u64_le = fun v #rrel #rel b pos ->
  let h = HST.get () in
  LE.writable_store_pre b (U32.v pos) 8 (fun s -> E.le_to_n s == U64.v v) h;
  LE.store64_le_i (* #(Ghost.hide rrel) #(Ghost.hide rel) *) b pos v;
  let h' = HST.get () in
  LE.store_post_modifies b (U32.v pos) 8 (fun s -> E.le_to_n s == U64.v v) h h';
  8ul

let write_u8 = leaf_writer_strong_of_serializer32 serialize32_u8 ()

let write_u16 = leaf_writer_strong_of_serializer32 serialize32_u16 ()

let write_u32 = leaf_writer_strong_of_serializer32 serialize32_u32 ()

let write_u64 = leaf_writer_strong_of_serializer32 serialize32_u64 ()

let write_u64_le = leaf_writer_strong_of_serializer32 serialize32_u64_le ()
