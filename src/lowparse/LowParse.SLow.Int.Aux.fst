module LowParse.SLow.Int.Aux
include LowParse.Spec.Int.Aux
include LowParse.SLow.Combinators

module Seq = FStar.Seq
module E = LowParse.BigEndianImpl.SLow
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = LowParse.Bytes32

inline_for_extraction
let serialize32_u8
: serializer32 serialize_u8
= (fun (input: U8.t) ->
    let b = B32.create 1ul input in
    B32.b32_reveal_create 1ul input;
    (b <: (res: bytes32 { serializer32_correct #_ #_ #parse_u8 serialize_u8 input res } )))

inline_for_extraction
let serialize32_u16 : serializer32 #_ #_ #parse_u16 serialize_u16 =
  (fun (input: U16.t) ->
    let b = E.n_to_be_2 _ _ (E.u16 ()) input in
    assert (E.n_to_be 2ul (U16.v input) == B32.reveal b);
    (b <: (res: B32.bytes { serializer32_correct #_ #_ #parse_u16 serialize_u16 input res } )))

inline_for_extraction
let serialize32_u32 : serializer32 #_ #_ #parse_u32 serialize_u32 =
  (fun (input: U32.t) ->
    let b = E.n_to_be_4 _ _ (E.u32 ()) input in
    assert (E.n_to_be 4ul (U32.v input) == B32.reveal b);
    (b <: (res: B32.bytes { serializer32_correct #_ #_ #parse_u32 serialize_u32 input res } )))

inline_for_extraction
let parse32_u16 : parser32 parse_u16 =
  decode_u16_injective ();
    make_total_constant_size_parser32 2 2ul
      #U16.t
      decode_u16
      ()
      (fun (input: B32.lbytes 2) ->
        let res = E.be_to_n_2 _ _ (E.u16 ()) input in
        (res <: (res: U16.t { res == decode_u16 (B32.reveal input) } )))

inline_for_extraction
let parse32_u32 : parser32 parse_u32 =
    decode_u32_injective ();
    make_total_constant_size_parser32 4 4ul
      #U32.t
      decode_u32
      ()
      (fun (input: B32.lbytes 4) ->
        let res = E.be_to_n_4 _ _ (E.u32 ()) input in
        (res <: (res: U32.t { res == decode_u32 (B32.reveal input) } )))

inline_for_extraction
let parse32_u8 : parser32 parse_u8 =
  decode_u8_injective ();
  make_total_constant_size_parser32 1 1ul
    decode_u8
    ()
    (fun (b: B32.lbytes 1) ->
      let r = B32.get b 0ul in
      assert (r == Seq.index (B32.reveal b) 0);
      B32.b32_index_reveal b 0;
      (r <: (y: U8.t { y == decode_u8 (B32.reveal b) })))
