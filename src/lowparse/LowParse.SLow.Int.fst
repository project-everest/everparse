module LowParse.SLow.Int
open LowParse.SLow.Combinators

module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module B32 = LowParse.Bytes32

friend LowParse.Spec.Int

let parse32_u8 =
  decode_u8_injective ();
  make_total_constant_size_parser32 1 1ul
    decode_u8
    ()
    (fun (b: B32.lbytes 1) ->
      let r = B32.get b 0ul in
      assert (r == Seq.index (B32.reveal b) 0);
      B32.b32_index_reveal b 0;
      (r <: (y: U8.t { y == decode_u8 (B32.reveal b) })))

let serialize32_u8
= (fun (input: U8.t) ->
    let b = B32.create 1ul input in
    B32.b32_reveal_create 1ul input;
    (b <: (res: bytes32 { serializer32_correct #_ #_ #parse_u8 serialize_u8 input res } )))

module E = LowParse.SLow.Endianness
module EI = LowParse.Spec.Endianness.Instances

inline_for_extraction
noextract
let be_to_n_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint16 2)

inline_for_extraction
let parse32_u16 : parser32 parse_u16 =
  decode_u16_injective ();
    make_total_constant_size_parser32 2 2ul
      #U16.t
      decode_u16
      ()
      (fun (input: B32.lbytes 2) -> be_to_n_2 input)

inline_for_extraction
noextract
let n_to_be_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be EI.uint16 2)

inline_for_extraction
let serialize32_u16
= (fun (input: U16.t) -> n_to_be_2 input)

inline_for_extraction
noextract
let be_to_n_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint32 4)

inline_for_extraction
let parse32_u32 : parser32 parse_u32 =
  decode_u32_injective ();
    make_total_constant_size_parser32 4 4ul
      #U32.t
      decode_u32
      ()
      (fun (input: B32.lbytes 4) -> be_to_n_4 input)

inline_for_extraction
noextract
let n_to_be_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be EI.uint32 4)

inline_for_extraction
let serialize32_u32
= (fun (input: U32.t) -> n_to_be_4 input)

inline_for_extraction
noextract
let be_to_n_8 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n EI.uint64 8)

inline_for_extraction
let parse32_u64 : parser32 parse_u64 =
  decode_u64_injective ();
    make_total_constant_size_parser32 8 8ul
      #U64.t
      decode_u64
      ()
      (fun (input: B32.lbytes 8) -> be_to_n_8 input)

inline_for_extraction
noextract
let n_to_be_8 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be EI.uint64 8)

inline_for_extraction
let serialize32_u64
= (fun (input: U64.t) -> n_to_be_8 input)
