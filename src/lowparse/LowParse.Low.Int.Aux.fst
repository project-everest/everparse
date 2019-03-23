module LowParse.Low.Int.Aux
include LowParse.Spec.Int.Aux
include LowParse.Low.Combinators

module Seq = FStar.Seq
module E = LowParse.BigEndianImpl.Low
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Buffer

inline_for_extraction
let read_u16 : leaf_reader parse_u16 =
  decode_u16_injective ();
    make_total_constant_size_reader 2 2ul
      #U16.t
      decode_u16
      ()
      (fun #rrel #rel input ->
        E.be_to_n_2 _ _ (E.u16 ()) input)

inline_for_extraction
let read_u32 : leaf_reader parse_u32 =
    decode_u32_injective ();
    make_total_constant_size_reader 4 4ul
      #U32.t
      decode_u32
      ()
      (fun #rrel #rel input ->
        E.be_to_n_4 _ _ (E.u32 ()) input)

inline_for_extraction
let read_u8 : leaf_reader parse_u8 =
  decode_u8_injective ();
  make_total_constant_size_reader 1 1ul
    decode_u8
    ()
    (fun #rrel #rel b pos -> B.index b pos)

module HST = FStar.HyperStack.ST

inline_for_extraction
let serialize32_u8 : serializer32 #_ #_ #parse_u8 serialize_u8 =
  fun v #rrel #rel out pos ->
  mbuffer_upd out (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 1)) pos v;
  1ul

inline_for_extraction
let serialize32_u16 : serializer32 #_ #_ #parse_u16 serialize_u16 =
  fun v #rrel #rel out pos ->
  E.n_to_be_2 U16.t 16 (E.u16 ()) v out pos;
  2ul

inline_for_extraction
let serialize32_u32 : serializer32 #_ #_ #parse_u32 serialize_u32 =
  fun v #rrel #rel out pos ->
  E.n_to_be_4 U32.t 32 (E.u32 ()) v out pos;
  4ul
