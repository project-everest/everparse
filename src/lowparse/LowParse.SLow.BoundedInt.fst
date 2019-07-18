module LowParse.SLow.BoundedInt

open LowParse.SLow.Combinators

module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module E = LowParse.BigEndianImpl.SLow
module Cast = FStar.Int.Cast

friend LowParse.Spec.BoundedInt


inline_for_extraction
let decode32_bounded_integer_1
  (b: B32.lbytes 1)
: Tot (y: bounded_integer 1 { y == decode_bounded_integer 1 (B32.reveal b) } )
= let r = E.be_to_n_1 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 1 { r == decode_bounded_integer 1 (B32.reveal b) } ))

inline_for_extraction
let decode32_bounded_integer_2
  (b: B32.lbytes 2)
: Tot (y: bounded_integer 2 { y == decode_bounded_integer 2 (B32.reveal b) } )
= let r = E.be_to_n_2 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 2 { r == decode_bounded_integer 2 (B32.reveal b) } ))

inline_for_extraction
let decode32_bounded_integer_3
  (b: B32.lbytes 3)
: Tot (y: bounded_integer 3 { y == decode_bounded_integer 3 (B32.reveal b) } )
= let r = E.be_to_n_3 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 3 { r == decode_bounded_integer 3 (B32.reveal b) } ))

inline_for_extraction
let decode32_bounded_integer_4
  (b: B32.lbytes 4)
: Tot (y: bounded_integer 4 { y == decode_bounded_integer 4 (B32.reveal b) } )
= let r = E.be_to_n_4 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 4 { r == decode_bounded_integer 4 (B32.reveal b) } ))

inline_for_extraction
let decode32_bounded_integer
  (sz: integer_size)
: Tot ((b: B32.lbytes sz) ->
    Tot (y: bounded_integer sz { y == decode_bounded_integer sz (B32.reveal b) } )
  )
= match sz with
  | 1 -> decode32_bounded_integer_1
  | 2 -> decode32_bounded_integer_2
  | 3 -> decode32_bounded_integer_3
  | 4 -> decode32_bounded_integer_4

inline_for_extraction
let parse32_bounded_integer' (sz: integer_size) : Tot (parser32 (parse_bounded_integer sz)) =
  [@inline_let]
  let _ = decode_bounded_integer_injective sz in
  make_total_constant_size_parser32 sz (U32.uint_to_t sz)
    (decode_bounded_integer sz)
    ()
    (decode32_bounded_integer sz)

let parse32_bounded_integer_1 = parse32_bounded_integer' 1
let parse32_bounded_integer_2 = parse32_bounded_integer' 2
let parse32_bounded_integer_3 = parse32_bounded_integer' 3
let parse32_bounded_integer_4 = parse32_bounded_integer' 4

inline_for_extraction
let serialize32_bounded_integer_1
: (serializer32 (serialize_bounded_integer 1))
= (fun (input: bounded_integer 1) ->
    let b = E.n_to_be_1 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 1) input res } ))
  )

inline_for_extraction
let serialize32_bounded_integer_2
: (serializer32 (serialize_bounded_integer 2))
= (fun (input: bounded_integer 2) ->
    let b = E.n_to_be_2 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 2) input res } ))
  )

inline_for_extraction
let serialize32_bounded_integer_3
: (serializer32 (serialize_bounded_integer 3))
= (fun (input: bounded_integer 3) ->
    let b = E.n_to_be_3 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 3) input res } ))
  )

inline_for_extraction
let serialize32_bounded_integer_4
: (serializer32 (serialize_bounded_integer 4))
= (fun (input: bounded_integer 4) ->
    let b = E.n_to_be_4 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 4) input res } ))
  )

inline_for_extraction
let bounded_integer_of_le_32_1
  (b: B32.lbytes 1)
: Tot (y: bounded_integer 1 { y == bounded_integer_of_le 1 (B32.reveal b) } )
= [@inline_let] let _ =
    bounded_integer_of_le_1_eq (B32.reveal b)
  in
  Cast.uint8_to_uint32 (B32.get b 0ul)

inline_for_extraction
let bounded_integer_of_le_32_2
  (b: B32.lbytes 2)
: Tot (y: bounded_integer 2 { y == bounded_integer_of_le 2 (B32.reveal b) } )
= [@inline_let] let _ =
    bounded_integer_of_le_2_eq (B32.reveal b)
  in
  Cast.uint8_to_uint32 (B32.get b 0ul) `U32.add` (256ul `U32.mul` Cast.uint8_to_uint32 (B32.get b 1ul))

inline_for_extraction
let bounded_integer_of_le_32_3
  (b: B32.lbytes 3)
: Tot (y: bounded_integer 3 { y == bounded_integer_of_le 3 (B32.reveal b) } )
= [@inline_let] let _ =
    bounded_integer_of_le_3_eq (B32.reveal b)
  in
  Cast.uint8_to_uint32 (B32.get b 0ul) `U32.add` (256ul `U32.mul` ( Cast.uint8_to_uint32 (B32.get b 1ul) `U32.add` (256ul `U32.mul` Cast.uint8_to_uint32 (B32.get b 2ul))))

inline_for_extraction
let bounded_integer_of_le_32_4
  (b: B32.lbytes 4)
: Tot (y: bounded_integer 4 { y == bounded_integer_of_le 4 (B32.reveal b) } )
= [@inline_let] let _ =
    bounded_integer_of_le_4_eq (B32.reveal b)
  in
  Cast.uint8_to_uint32 (B32.get b 0ul) `U32.add` (256ul `U32.mul` ( Cast.uint8_to_uint32 (B32.get b 1ul) `U32.add` (256ul `U32.mul` (Cast.uint8_to_uint32 (B32.get b 2ul) `U32.add` (256ul `U32.mul` Cast.uint8_to_uint32 (B32.get b 3ul))))))

let parse32_bounded_integer_le_1
= [@inline_let] let _ =
    bounded_integer_of_le_injective 1
  in
  make_total_constant_size_parser32
    1
    1ul
    (bounded_integer_of_le 1)
    ()
    bounded_integer_of_le_32_1

let parse32_bounded_integer_le_2
= [@inline_let] let _ =
    bounded_integer_of_le_injective 2
  in
  make_total_constant_size_parser32
    2
    2ul
    (bounded_integer_of_le 2)
    ()
    bounded_integer_of_le_32_2

let parse32_bounded_integer_le_3
= [@inline_let] let _ =
    bounded_integer_of_le_injective 3
  in
  make_total_constant_size_parser32
    3
    3ul
    (bounded_integer_of_le 3)
    ()
    bounded_integer_of_le_32_3

let parse32_bounded_integer_le_4
= [@inline_let] let _ =
    bounded_integer_of_le_injective 4
  in
  make_total_constant_size_parser32
    4
    4ul
    (bounded_integer_of_le 4)
    ()
    bounded_integer_of_le_32_4


let parse32_u16_le =
  parse32_synth'
    _
    synth_u16_le
    parse32_bounded_integer_le_2
    ()

let parse32_u32_le =
  parse32_synth'
    _
    synth_u32_le
    parse32_bounded_integer_le_4
    ()

let serialize32_bounded_integer_le_1 = fun (x: bounded_integer 1) -> ((
    [@inline_let] let _ =
      serialize_bounded_integer_le_1_eq x 0
    in
    B32.create 1ul (Cast.uint32_to_uint8 x)
  ) <: (res: bytes32 { serializer32_correct' (serialize_bounded_integer_le 1) x res } ))

let serialize32_bounded_integer_le_2
= fun (x: bounded_integer 2) -> ((
    [@inline_let] let _ =
      serialize_bounded_integer_le_2_eq x 0;
      serialize_bounded_integer_le_2_eq x 1
    in
    B32.create 1ul (Cast.uint32_to_uint8 x) `B32.append` B32.create 1ul (Cast.uint32_to_uint8 (x `U32.div` 256ul))
  ) <: (res: bytes32 { serializer32_correct' (serialize_bounded_integer_le 2) x res } ))

let serialize32_bounded_integer_le_3
= fun (x: bounded_integer 3) -> ((
    [@inline_let] let _ =
      serialize_bounded_integer_le_3_eq x 0;
      serialize_bounded_integer_le_3_eq x 1;
      serialize_bounded_integer_le_3_eq x 2
    in
    let rem0 = Cast.uint32_to_uint8 x in
    let div0 = x `U32.div` 256ul in
    let rem1 = Cast.uint32_to_uint8 div0 in
    let div1 = div0 `U32.div` 256ul in
    let rem2 = Cast.uint32_to_uint8 div1 in
    (B32.create 1ul rem0 `B32.append` B32.create 1ul rem1) `B32.append`
    B32.create 1ul rem2
  ) <: (res: bytes32 { serializer32_correct' (serialize_bounded_integer_le 3) x res } ))

let serialize32_bounded_integer_le_4
= fun (x: bounded_integer 4) -> ((
    [@inline_let] let _ =
      serialize_bounded_integer_le_4_eq x 0;
      serialize_bounded_integer_le_4_eq x 1;
      serialize_bounded_integer_le_4_eq x 2;
      serialize_bounded_integer_le_4_eq x 3
    in
    let rem0 = Cast.uint32_to_uint8 x in
    let div0 = x `U32.div` 256ul in
    let rem1 = Cast.uint32_to_uint8 div0 in
    let div1 = div0 `U32.div` 256ul in
    let rem2 = Cast.uint32_to_uint8 div1 in
    let div2 = div1 `U32.div` 256ul in
    let rem3 = Cast.uint32_to_uint8 div2 in
    (B32.create 1ul rem0 `B32.append` B32.create 1ul rem1) `B32.append`
    (B32.create 1ul rem2 `B32.append` B32.create 1ul rem3)
  ) <: (res: bytes32 { serializer32_correct' (serialize_bounded_integer_le 4) x res } ))

let serialize32_u16_le =
  serialize32_synth' 
    _
    synth_u16_le
    _
    serialize32_bounded_integer_le_2
    synth_u16_le_recip
    ()

let serialize32_u32_le =
  serialize32_synth' 
    _
    synth_u32_le
    _
    serialize32_bounded_integer_le_4
    synth_u32_le_recip
    ()

inline_for_extraction
let parse32_bounded_int32'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz32: U32.t { log256' (U32.v max32) == U32.v sz32 })
: Tot (parser32 (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= [@inline_let]
  let sz = U32.v sz32 in
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  parse32_synth
    (parse_bounded_integer sz `parse_filter` in_bounds min max)
    (fun x -> (x <: bounded_int32 min max))
    (fun x -> x)
    (parse32_filter (parse32_bounded_integer sz) (in_bounds min max) (fun x -> not (x `U32.lt` min32 || max32 `U32.lt` x)))
    ()

let parse32_bounded_int32_1
  min max
= parse32_bounded_int32' min max 1ul

let parse32_bounded_int32_2
  min max
= parse32_bounded_int32' min max 2ul

let parse32_bounded_int32_3
  min max
= parse32_bounded_int32' min max 3ul

let parse32_bounded_int32_4
  min max
= parse32_bounded_int32' min max 4ul

inline_for_extraction
let serialize32_bounded_int32'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz32: U32.t { log256' (U32.v max32) == U32.v sz32 })
: Tot (serializer32 (serialize_bounded_int32 (U32.v min32) (U32.v max32)))
= [@inline_let]
  let sz = U32.v sz32 in
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  serialize32_synth
    (parse_bounded_integer sz `parse_filter` in_bounds min max)
    (fun x -> (x <: bounded_int32 min max))
    _
    (serialize32_filter (serialize32_bounded_integer sz) (in_bounds min max))
    (fun x -> x)
    (fun x -> x)
    ()

let serialize32_bounded_int32_1
  min max
= serialize32_bounded_int32' min max 1ul

let serialize32_bounded_int32_2
  min max
= serialize32_bounded_int32' min max 2ul

let serialize32_bounded_int32_3
  min max
= serialize32_bounded_int32' min max 3ul

let serialize32_bounded_int32_4
  min max
= serialize32_bounded_int32' min max 4ul


inline_for_extraction
let parse32_bounded_int32_le'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz32: U32.t { log256' (U32.v max32) == U32.v sz32 })
: Tot (parser32 (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= [@inline_let]
  let sz = U32.v sz32 in
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  parse32_synth
    (parse_bounded_integer_le sz `parse_filter` in_bounds min max)
    (fun x -> (x <: bounded_int32 min max))
    (fun x -> x)
    (parse32_filter (parse32_bounded_integer_le sz) (in_bounds min max) (fun x -> not (x `U32.lt` min32 || max32 `U32.lt` x)))
    ()

let parse32_bounded_int32_le_1
  min max
= parse32_bounded_int32_le' min max 1ul

let parse32_bounded_int32_le_2
  min max
= parse32_bounded_int32_le' min max 2ul

let parse32_bounded_int32_le_3
  min max
= parse32_bounded_int32_le' min max 3ul

let parse32_bounded_int32_le_4
  min max
= parse32_bounded_int32_le' min max 4ul

inline_for_extraction
let serialize32_bounded_int32_le'
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
  (sz32: U32.t { log256' (U32.v max32) == U32.v sz32 })
: Tot (serializer32 (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))
= [@inline_let]
  let sz = U32.v sz32 in
  [@inline_let]
  let min = U32.v min32 in
  [@inline_let]
  let max = U32.v max32 in
  serialize32_synth
    (parse_bounded_integer_le sz `parse_filter` in_bounds min max)
    (fun x -> (x <: bounded_int32 min max))
    _
    (serialize32_filter (serialize32_bounded_integer_le sz) (in_bounds min max))
    (fun x -> x)
    (fun x -> x)
    ()

let serialize32_bounded_int32_le_1
  min max
= serialize32_bounded_int32_le' min max 1ul

let serialize32_bounded_int32_le_2
  min max
= serialize32_bounded_int32_le' min max 2ul

let serialize32_bounded_int32_le_3
  min max
= serialize32_bounded_int32_le' min max 3ul

let serialize32_bounded_int32_le_4
  min max
= serialize32_bounded_int32_le' min max 4ul
