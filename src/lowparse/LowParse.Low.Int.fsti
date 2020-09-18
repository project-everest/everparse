module LowParse.Low.Int
include LowParse.Spec.Int
include LowParse.Low.Base

inline_for_extraction
val read_u8: leaf_reader parse_u8

inline_for_extraction
val read_u16: leaf_reader parse_u16

inline_for_extraction
val read_u32: leaf_reader parse_u32

inline_for_extraction
val read_u64 : leaf_reader parse_u64

inline_for_extraction
val read_u64_le : leaf_reader parse_u64_le

inline_for_extraction
let validate_u8 () : validator parse_u8 =
  validate_total_constant_size parse_u8 1uL ()

inline_for_extraction
let validate_u8_with_error_code (c: error_code) : validator parse_u8 =
  validate_total_constant_size_with_error_code parse_u8 1uL c

inline_for_extraction
let validate_u16 () : validator parse_u16 =
  validate_total_constant_size parse_u16 2uL ()

inline_for_extraction
let validate_u32 () : validator parse_u32 =
  validate_total_constant_size parse_u32 4uL ()

inline_for_extraction
let validate_u64 () : validator parse_u64 =
  validate_total_constant_size parse_u64 8uL ()

inline_for_extraction
let validate_u64_le () : validator parse_u64_le =
  validate_total_constant_size parse_u64_le 8uL ()

inline_for_extraction
let validate_u64_le_with_error_code (c: error_code) : validator parse_u64_le =
  validate_total_constant_size_with_error_code parse_u64_le 8uL c

inline_for_extraction
let jump_u8 : jumper parse_u8 =
  jump_constant_size parse_u8 1ul ()

inline_for_extraction
let jump_u16 : jumper parse_u16 =
  jump_constant_size parse_u16 2ul ()

inline_for_extraction
let jump_u32 : jumper parse_u32 =
  jump_constant_size parse_u32 4ul ()

inline_for_extraction
let jump_u64 : jumper parse_u64 =
  jump_constant_size parse_u64 8ul ()

inline_for_extraction
let jump_u64_le : jumper parse_u64_le =
  jump_constant_size parse_u64_le 8ul ()

inline_for_extraction
val serialize32_u8 : serializer32 serialize_u8

inline_for_extraction
val serialize32_u16 : serializer32 serialize_u16

inline_for_extraction
val serialize32_u32 : serializer32 serialize_u32

inline_for_extraction
val serialize32_u64 : serializer32 serialize_u64

inline_for_extraction
val write_u8 : leaf_writer_strong serialize_u8

inline_for_extraction
let write_u8_weak : leaf_writer_weak serialize_u8 =
  leaf_writer_weak_of_strong_constant_size write_u8 1ul ()

inline_for_extraction
val write_u16 : leaf_writer_strong serialize_u16

inline_for_extraction
let write_u16_weak : leaf_writer_weak serialize_u16 =
  leaf_writer_weak_of_strong_constant_size write_u16 2ul ()

inline_for_extraction
val write_u32 : leaf_writer_strong serialize_u32

inline_for_extraction
let write_u32_weak : leaf_writer_weak serialize_u32 =
  leaf_writer_weak_of_strong_constant_size write_u32 4ul ()

inline_for_extraction
val write_u64 : leaf_writer_strong serialize_u64

inline_for_extraction
let write_u64_weak : leaf_writer_weak serialize_u64 =
  leaf_writer_weak_of_strong_constant_size write_u64 8ul ()

inline_for_extraction
val write_u64_le : leaf_writer_strong serialize_u64_le

inline_for_extraction
let write_u64_le_weak : leaf_writer_weak serialize_u64_le =
  leaf_writer_weak_of_strong_constant_size write_u64_le 8ul ()
