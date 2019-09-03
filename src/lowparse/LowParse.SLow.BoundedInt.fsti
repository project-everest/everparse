module LowParse.SLow.BoundedInt
include LowParse.Spec.BoundedInt
include LowParse.SLow.Base

(* bounded integers *)

inline_for_extraction
val parse32_bounded_integer_1
: (parser32 (parse_bounded_integer 1))

inline_for_extraction
val parse32_bounded_integer_2
: (parser32 (parse_bounded_integer 2))

inline_for_extraction
val parse32_bounded_integer_3
: (parser32 (parse_bounded_integer 3))

inline_for_extraction
val parse32_bounded_integer_4
: (parser32 (parse_bounded_integer 4))

inline_for_extraction
noextract
let parse32_bounded_integer (sz: integer_size) : Tot (parser32 (parse_bounded_integer sz))
= match sz with
  | 1 -> parse32_bounded_integer_1
  | 2 -> parse32_bounded_integer_2
  | 3 -> parse32_bounded_integer_3
  | 4 -> parse32_bounded_integer_4

inline_for_extraction
val serialize32_bounded_integer_1
: (serializer32 (serialize_bounded_integer 1))

inline_for_extraction
val serialize32_bounded_integer_2
: (serializer32 (serialize_bounded_integer 2))

inline_for_extraction
val serialize32_bounded_integer_3
: (serializer32 (serialize_bounded_integer 3))

inline_for_extraction
val serialize32_bounded_integer_4
: (serializer32 (serialize_bounded_integer 4))

inline_for_extraction
noextract
let serialize32_bounded_integer
  (sz: integer_size)
: Tot (serializer32 (serialize_bounded_integer sz))
= match sz with
  | 1 -> serialize32_bounded_integer_1
  | 2 -> serialize32_bounded_integer_2
  | 3 -> serialize32_bounded_integer_3
  | 4 -> serialize32_bounded_integer_4

#push-options "--max_fuel 0"

inline_for_extraction
val parse32_bounded_integer_le_1
: parser32 (parse_bounded_integer_le 1)

inline_for_extraction
val parse32_bounded_integer_le_2
: parser32 (parse_bounded_integer_le 2)

inline_for_extraction
val parse32_bounded_integer_le_3
: parser32 (parse_bounded_integer_le 3)

inline_for_extraction
val parse32_bounded_integer_le_4
: parser32 (parse_bounded_integer_le 4)

inline_for_extraction
noextract
let parse32_bounded_integer_le (sz: integer_size) : Tot (parser32 (parse_bounded_integer_le sz))
= match sz with
  | 1 -> parse32_bounded_integer_le_1
  | 2 -> parse32_bounded_integer_le_2
  | 3 -> parse32_bounded_integer_le_3
  | 4 -> parse32_bounded_integer_le_4

inline_for_extraction
val parse32_u16_le : parser32 parse_u16_le

inline_for_extraction
val parse32_u32_le : parser32 parse_u32_le

#pop-options

inline_for_extraction
val serialize32_bounded_integer_le_1  : serializer32 (serialize_bounded_integer_le 1)

inline_for_extraction
val serialize32_bounded_integer_le_2  : serializer32 (serialize_bounded_integer_le 2)

inline_for_extraction
val serialize32_bounded_integer_le_3  : serializer32 (serialize_bounded_integer_le 3)

inline_for_extraction
val serialize32_bounded_integer_le_4  : serializer32 (serialize_bounded_integer_le 4)

inline_for_extraction
noextract
let serialize32_bounded_integer_le (sz: integer_size) : Tot (serializer32 (serialize_bounded_integer_le sz))
= match sz with
  | 1 -> serialize32_bounded_integer_le_1
  | 2 -> serialize32_bounded_integer_le_2
  | 3 -> serialize32_bounded_integer_le_3
  | 4 -> serialize32_bounded_integer_le_4

inline_for_extraction
val serialize32_u16_le : serializer32 serialize_u16_le

inline_for_extraction
val serialize32_u32_le : serializer32 serialize_u32_le

inline_for_extraction
let size32_u16_le: size32 serialize_u16_le =
  assert_norm (size32_constant_precond serialize_u16_le 2ul);
  size32_constant serialize_u16_le 2ul ()

inline_for_extraction
let size32_u32_le: size32 serialize_u32_le =
  assert_norm (size32_constant_precond serialize_u32_le 4ul);
  size32_constant serialize_u32_le 4ul ()

module U32 = FStar.UInt32

val parse32_bounded_int32_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (parser32 (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val parse32_bounded_int32_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (parser32 (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val parse32_bounded_int32_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (parser32 (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val parse32_bounded_int32_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (parser32 (parse_bounded_int32 (U32.v min32) (U32.v max32)))

inline_for_extraction
let parse32_bounded_int32
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (parser32 (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= fun input -> (
  if max32 `U32.lt` 256ul
  then parse32_bounded_int32_1 min32 max32 input
  else if max32 `U32.lt` 65536ul
  then parse32_bounded_int32_2 min32 max32 input
  else if max32 `U32.lt` 16777216ul
  then parse32_bounded_int32_3 min32 max32 input
  else parse32_bounded_int32_4 min32 max32 input
  )

val serialize32_bounded_int32_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (serializer32 (serialize_bounded_int32 (U32.v min32) (U32.v max32)))

val serialize32_bounded_int32_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (serializer32 (serialize_bounded_int32 (U32.v min32) (U32.v max32)))

val serialize32_bounded_int32_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (serializer32 (serialize_bounded_int32 (U32.v min32) (U32.v max32)))

val serialize32_bounded_int32_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (serializer32 (serialize_bounded_int32 (U32.v min32) (U32.v max32)))

inline_for_extraction
let serialize32_bounded_int32
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (serializer32 (serialize_bounded_int32 (U32.v min32) (U32.v max32)))
= fun input -> (
  if max32 `U32.lt` 256ul
  then serialize32_bounded_int32_1 min32 max32 input
  else if max32 `U32.lt` 65536ul
  then serialize32_bounded_int32_2 min32 max32 input
  else if max32 `U32.lt` 16777216ul
  then serialize32_bounded_int32_3 min32 max32 input
  else serialize32_bounded_int32_4 min32 max32 input
  )


val parse32_bounded_int32_le_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (parser32 (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val parse32_bounded_int32_le_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (parser32 (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val parse32_bounded_int32_le_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (parser32 (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val parse32_bounded_int32_le_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (parser32 (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

inline_for_extraction
let parse32_bounded_int32_le
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (parser32 (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= fun input -> (
  if max32 `U32.lt` 256ul
  then parse32_bounded_int32_le_1 min32 max32 input
  else if max32 `U32.lt` 65536ul
  then parse32_bounded_int32_le_2 min32 max32 input
  else if max32 `U32.lt` 16777216ul
  then parse32_bounded_int32_le_3 min32 max32 input
  else parse32_bounded_int32_le_4 min32 max32 input
  )

val serialize32_bounded_int32_le_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (serializer32 (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))

val serialize32_bounded_int32_le_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (serializer32 (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))

val serialize32_bounded_int32_le_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (serializer32 (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))

val serialize32_bounded_int32_le_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (serializer32 (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))

inline_for_extraction
let serialize32_bounded_int32_le
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (serializer32 (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))
= fun input -> (
  if max32 `U32.lt` 256ul
  then serialize32_bounded_int32_le_1 min32 max32 input
  else if max32 `U32.lt` 65536ul
  then serialize32_bounded_int32_le_2 min32 max32 input
  else if max32 `U32.lt` 16777216ul
  then serialize32_bounded_int32_le_3 min32 max32 input
  else serialize32_bounded_int32_le_4 min32 max32 input
  )

val parse32_bounded_int32_le_fixed_size
  (min32: U32.t)
  (max32: U32.t { U32.v min32 <= U32.v max32 })
: Tot (parser32 (parse_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32)))

val serialize32_bounded_int32_le_fixed_size
  (min32: U32.t)
  (max32: U32.t { U32.v min32 <= U32.v max32 })
: Tot (serializer32 (serialize_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32)))
  
