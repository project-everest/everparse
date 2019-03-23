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
val parse32_bounded_integer_le_4
: parser32 (parse_bounded_integer_le 4)

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
val serialize32_bounded_integer_le_4  : serializer32 (serialize_bounded_integer_le 4)

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

