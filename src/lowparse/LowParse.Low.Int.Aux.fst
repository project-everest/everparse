module LowParse.Low.Int.Aux
include LowParse.Spec.Int.Aux
include LowParse.Low.Combinators

module Seq = FStar.Seq
module E = LowParse.BigEndianImpl.Low
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
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
module Cast = FStar.Int.Cast

#push-options "--z3rlimit 16"

inline_for_extraction
let read_u64 : leaf_reader parse_u64 =
  decode_u64_injective ();
  make_total_constant_size_reader 8 8ul
    decode_u64
    ()
    (fun #rrel #rel b pos ->
      let h = HST.get () in
      [@inline_let] let _ = decode_u64_eq (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 8)) in
      let r7 = B.index b pos in
      let r6 = B.index b (pos `U32.add` 1ul) in
      let r5 = B.index b (pos `U32.add` 2ul) in
      let r4 = B.index b (pos `U32.add` 3ul) in
      let r3 = B.index b (pos `U32.add` 4ul) in
      let r2 = B.index b (pos `U32.add` 5ul) in
      let r1 = B.index b (pos `U32.add` 6ul) in
      let r0 = B.index b (pos `U32.add` 7ul) in
      Cast.uint8_to_uint64 r0 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r1 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r2 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r3 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r4 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r5 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r6 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r7
    )))))))))))))))

inline_for_extraction
let read_u64_le : leaf_reader parse_u64_le =
  decode_u64_le_injective ();
  make_total_constant_size_reader 8 8ul
    decode_u64_le
    ()
    (fun #rrel #rel b pos ->
      let h = HST.get () in
      [@inline_let] let _ = decode_u64_le_eq (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 8)) in
      let r0 = B.index b pos in
      let r1 = B.index b (pos `U32.add` 1ul) in
      let r2 = B.index b (pos `U32.add` 2ul) in
      let r3 = B.index b (pos `U32.add` 3ul) in
      let r4 = B.index b (pos `U32.add` 4ul) in
      let r5 = B.index b (pos `U32.add` 5ul) in
      let r6 = B.index b (pos `U32.add` 6ul) in
      let r7 = B.index b (pos `U32.add` 7ul) in
      Cast.uint8_to_uint64 r0 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r1 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r2 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r3 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r4 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r5 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r6 `U64.add` (256uL `U64.mul` (
      Cast.uint8_to_uint64 r7
    )))))))))))))))

#pop-options

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

#push-options "--z3rlimit 32"

inline_for_extraction
let serialize32_u64 : serializer32 serialize_u64 =
  fun v #rrel #rel b pos ->
  [@inline_let]
  let _ =
    serialize_u64_eq v 0;
    serialize_u64_eq v 1;
    serialize_u64_eq v 2;
    serialize_u64_eq v 3;
    serialize_u64_eq v 4;
    serialize_u64_eq v 5;
    serialize_u64_eq v 6;
    serialize_u64_eq v 7
  in
  let r7 = Cast.uint64_to_uint8 v in
  let d7 = v `U64.div` 256uL in
  let r6 = Cast.uint64_to_uint8 d7 in
  let d6 = d7 `U64.div` 256uL in
  let r5 = Cast.uint64_to_uint8 d6 in
  let d5 = d6 `U64.div` 256uL in
  let r4 = Cast.uint64_to_uint8 d5 in
  let d4 = d5 `U64.div` 256uL in
  let r3 = Cast.uint64_to_uint8 d4 in
  let d3 = d4 `U64.div` 256uL in
  let r2 = Cast.uint64_to_uint8 d3 in
  let d2 = d3 `U64.div` 256uL in
  let r1 = Cast.uint64_to_uint8 d2 in
  let d1 = d2 `U64.div` 256uL in
  let r0 = Cast.uint64_to_uint8 d1 in
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) pos r0;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 1ul) r1;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 2ul) r2;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 3ul) r3;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 4ul) r4;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 5ul) r5;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 6ul) r6;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 7ul) r7;
  8ul

inline_for_extraction
let serialize32_u64_le : serializer32 serialize_u64_le =
  fun v #rrel #rel b pos ->
  [@inline_let]
  let _ =
    serialize_u64_le_eq v 0;
    serialize_u64_le_eq v 1;
    serialize_u64_le_eq v 2;
    serialize_u64_le_eq v 3;
    serialize_u64_le_eq v 4;
    serialize_u64_le_eq v 5;
    serialize_u64_le_eq v 6;
    serialize_u64_le_eq v 7
  in
  let r0 = Cast.uint64_to_uint8 v in
  let d0 = v `U64.div` 256uL in
  let r1 = Cast.uint64_to_uint8 d0 in
  let d1 = d0 `U64.div` 256uL in
  let r2 = Cast.uint64_to_uint8 d1 in
  let d2 = d1 `U64.div` 256uL in
  let r3 = Cast.uint64_to_uint8 d2 in
  let d3 = d2 `U64.div` 256uL in
  let r4 = Cast.uint64_to_uint8 d3 in
  let d4 = d3 `U64.div` 256uL in
  let r5 = Cast.uint64_to_uint8 d4 in
  let d5 = d4 `U64.div` 256uL in
  let r6 = Cast.uint64_to_uint8 d5 in
  let d6 = d5 `U64.div` 256uL in
  let r7 = Cast.uint64_to_uint8 d6 in
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) pos r0;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 1ul) r1;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 2ul) r2;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 3ul) r3;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 4ul) r4;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 5ul) r5;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 6ul) r6;
  mbuffer_upd b (Ghost.hide (U32.v pos)) (Ghost.hide (U32.v pos + 8)) (pos `U32.add` 7ul) r7;
  8ul

#pop-options
