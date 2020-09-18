module LowParse.SLow.Int
include LowParse.Spec.Int
include LowParse.SLow.Base

inline_for_extraction
val parse32_u8: parser32 parse_u8

inline_for_extraction
val serialize32_u8 : serializer32 serialize_u8

inline_for_extraction
val parse32_u16: parser32 parse_u16

inline_for_extraction
val serialize32_u16 : serializer32 serialize_u16

inline_for_extraction
val parse32_u32: parser32 parse_u32

inline_for_extraction
val serialize32_u32 : serializer32 serialize_u32

inline_for_extraction
val parse32_u64: parser32 parse_u64

inline_for_extraction
val serialize32_u64 : serializer32 serialize_u64

// the `assert_norm`s are for the .fst, interleaving semantics again

inline_for_extraction
let size32_u8: size32 serialize_u8 =
  assert_norm (size32_constant_precond serialize_u8 1ul);
  size32_constant serialize_u8 1ul ()

inline_for_extraction
let size32_u16: size32 serialize_u16 =
  assert_norm (size32_constant_precond serialize_u16 2ul);
  size32_constant serialize_u16 2ul ()

inline_for_extraction
let size32_u32: size32 serialize_u32 =
  assert_norm (size32_constant_precond serialize_u32 4ul);
  size32_constant serialize_u32 4ul ()

inline_for_extraction
let size32_u64: size32 serialize_u64 =
  assert_norm (size32_constant_precond serialize_u64 8ul);
  size32_constant serialize_u64 8ul ()
