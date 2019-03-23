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
      (fun input ->
        E.be_to_n_2 _ _ (E.u16 ()) input)

inline_for_extraction
let read_u32 : leaf_reader parse_u32 =
    decode_u32_injective ();
    make_total_constant_size_reader 4 4ul
      #U32.t
      decode_u32
      ()
      (fun input ->
        E.be_to_n_4 _ _ (E.u32 ()) input)

inline_for_extraction
let read_u8 : leaf_reader parse_u8 =
  decode_u8_injective ();
  make_total_constant_size_reader 1 1ul
    decode_u8
    ()
    (fun b -> B.index b 0ul)

inline_for_extraction
let serialize32_u8 : serializer32 #_ #_ #parse_u8 serialize_u8 =
  fun v out ->
  let out' = B.sub out 0ul 1ul in
  B.upd out' 0ul v;
  1ul

inline_for_extraction
let serialize32_u16 : serializer32 #_ #_ #parse_u16 serialize_u16 =
  fun v out ->
  let out' = B.sub out 0ul 2ul in
  E.n_to_be_2 U16.t 16 (E.u16 ()) v out';
  2ul

inline_for_extraction
let serialize32_u32 : serializer32 #_ #_ #parse_u32 serialize_u32 =
  fun v out ->
  let out' = B.sub out 0ul 4ul in
  E.n_to_be_4 U32.t 32 (E.u32 ()) v out';
  4ul
