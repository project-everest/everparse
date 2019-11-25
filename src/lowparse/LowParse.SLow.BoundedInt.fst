module LowParse.SLow.BoundedInt

open LowParse.SLow.Combinators

module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module E = LowParse.SLow.Endianness
module EI = LowParse.Spec.Endianness.Instances
module Cast = FStar.Int.Cast

friend LowParse.Spec.BoundedInt

inline_for_extraction
noextract
let be_to_n_1 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n (EI.bounded_integer 1) 1)

inline_for_extraction
let decode32_bounded_integer_1
  (b: B32.lbytes 1)
: Tot (y: bounded_integer 1 { y == decode_bounded_integer 1 (B32.reveal b) } )
= be_to_n_1 b

inline_for_extraction
noextract
let be_to_n_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n (EI.bounded_integer 2) 2)

inline_for_extraction
let decode32_bounded_integer_2
  (b: B32.lbytes 2)
: Tot (y: bounded_integer 2 { y == decode_bounded_integer 2 (B32.reveal b) } )
= be_to_n_2 b

inline_for_extraction
noextract
let be_to_n_3 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n (EI.bounded_integer 3) 3)

inline_for_extraction
let decode32_bounded_integer_3
  (b: B32.lbytes 3)
: Tot (y: bounded_integer 3 { y == decode_bounded_integer 3 (B32.reveal b) } )
= be_to_n_3 b

inline_for_extraction
noextract
let be_to_n_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_be_to_n (EI.bounded_integer 4) 4)

inline_for_extraction
let decode32_bounded_integer_4
  (b: B32.lbytes 4)
: Tot (y: bounded_integer 4 { y == decode_bounded_integer 4 (B32.reveal b) } )
= be_to_n_4 b

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
noextract
let n_to_be_1 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be (EI.bounded_integer 1) 1)

inline_for_extraction
let serialize32_bounded_integer_1
: (serializer32 (serialize_bounded_integer 1))
= (fun (input: bounded_integer 1) ->
    n_to_be_1 input)

inline_for_extraction
noextract
let n_to_be_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be (EI.bounded_integer 2) 2)

inline_for_extraction
let serialize32_bounded_integer_2
: (serializer32 (serialize_bounded_integer 2))
= (fun (input: bounded_integer 2) ->
    n_to_be_2 input)

inline_for_extraction
noextract
let n_to_be_3 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be (EI.bounded_integer 3) 3)

inline_for_extraction
let serialize32_bounded_integer_3
: (serializer32 (serialize_bounded_integer 3))
= (fun (input: bounded_integer 3) ->
    n_to_be_3 input)

inline_for_extraction
noextract
let n_to_be_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_be (EI.bounded_integer 4) 4)

inline_for_extraction
let serialize32_bounded_integer_4
: (serializer32 (serialize_bounded_integer 4))
= (fun (input: bounded_integer 4) ->
    n_to_be_4 input)

inline_for_extraction
noextract
let le_to_n_1 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_le_to_n (EI.bounded_integer 1) 1)

inline_for_extraction
let bounded_integer_of_le_32_1
  (b: B32.lbytes 1)
: Tot (y: bounded_integer 1 { y == bounded_integer_of_le 1 (B32.reveal b) } )
= le_to_n_1 b

inline_for_extraction
noextract
let le_to_n_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_le_to_n (EI.bounded_integer 2) 2)

inline_for_extraction
let bounded_integer_of_le_32_2
  (b: B32.lbytes 2)
: Tot (y: bounded_integer 2 { y == bounded_integer_of_le 2 (B32.reveal b) } )
= le_to_n_2 b

inline_for_extraction
noextract
let le_to_n_3 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_le_to_n (EI.bounded_integer 3) 3)

inline_for_extraction
let bounded_integer_of_le_32_3
  (b: B32.lbytes 3)
: Tot (y: bounded_integer 3 { y == bounded_integer_of_le 3 (B32.reveal b) } )
= le_to_n_3 b

inline_for_extraction
noextract
let le_to_n_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_le_to_n (EI.bounded_integer 4) 4)

inline_for_extraction
let bounded_integer_of_le_32_4
  (b: B32.lbytes 4)
: Tot (y: bounded_integer 4 { y == bounded_integer_of_le 4 (B32.reveal b) } )
= le_to_n_4 b

inline_for_extraction
let bounded_integer_of_le_32
  (sz: integer_size)
: Tot ((b: B32.lbytes sz) ->
    Tot (y: bounded_integer sz { y == bounded_integer_of_le sz (B32.reveal b) } )
  )
= match sz with
  | 1 -> bounded_integer_of_le_32_1
  | 2 -> bounded_integer_of_le_32_2
  | 3 -> bounded_integer_of_le_32_3
  | 4 -> bounded_integer_of_le_32_4

inline_for_extraction
let parse32_bounded_integer_le' (sz: integer_size) : Tot (parser32 (parse_bounded_integer_le sz)) =
  [@inline_let]
  let _ = bounded_integer_of_le_injective sz in
  make_total_constant_size_parser32 sz (U32.uint_to_t sz)
    (bounded_integer_of_le sz)
    ()
    (bounded_integer_of_le_32 sz)

let parse32_bounded_integer_le_1 = parse32_bounded_integer_le' 1
let parse32_bounded_integer_le_2 = parse32_bounded_integer_le' 2
let parse32_bounded_integer_le_3 = parse32_bounded_integer_le' 3
let parse32_bounded_integer_le_4 = parse32_bounded_integer_le' 4

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

inline_for_extraction
noextract
let n_to_le_1 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_le (EI.bounded_integer 1) 1)

let serialize32_bounded_integer_le_1 = fun (x: bounded_integer 1) ->
  n_to_le_1 x

inline_for_extraction
noextract
let n_to_le_2 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_le (EI.bounded_integer 2) 2)

let serialize32_bounded_integer_le_2 = fun (x: bounded_integer 2) ->
  n_to_le_2 x

inline_for_extraction
noextract
let n_to_le_3 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_le (EI.bounded_integer 3) 3)

let serialize32_bounded_integer_le_3 = fun (x: bounded_integer 3) ->
  n_to_le_3 x

inline_for_extraction
noextract
let n_to_le_4 = norm [delta_attr [`%E.must_reduce]; iota; zeta; primops] (E.mk_n_to_le (EI.bounded_integer 4) 4)

let serialize32_bounded_integer_le_4 = fun (x: bounded_integer 4) ->
  n_to_le_4 x

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

let parse32_bounded_int32_le_fixed_size
  min32 max32
= parse32_filter parse32_u32_le (in_bounds (U32.v min32) (U32.v max32)) (fun x -> not (x `U32.lt` min32 || max32 `U32.lt` x))

let serialize32_bounded_int32_le_fixed_size
  min32 max32
= serialize32_filter serialize32_u32_le (in_bounds (U32.v min32) (U32.v max32))
