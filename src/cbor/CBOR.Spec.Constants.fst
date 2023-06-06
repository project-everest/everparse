module CBOR.Spec.Constants
open LowParse.Spec.BitSum

inline_for_extraction
noextract
let major_type_t = bitfield uint8 3

[@@CMacro]
let major_type_simple_value : major_type_t = 7uy

[@@CMacro]
let major_type_uint64 : major_type_t = 0uy

[@@CMacro]
let major_type_neg_int64 : major_type_t = 1uy

inline_for_extraction
noextract
let major_type_uint64_or_neg_int64 : eqtype = (x: major_type_t { x == major_type_uint64 \/ x == major_type_neg_int64 })

[@@CMacro]
let major_type_byte_string : major_type_t = 2uy

[@@CMacro]
let major_type_text_string : major_type_t = 3uy

inline_for_extraction
noextract
let major_type_byte_string_or_text_string : eqtype = (x: major_type_t { x == major_type_byte_string \/ x == major_type_text_string })

[@@CMacro]
let major_type_array : major_type_t = 4uy

[@@CMacro]
let major_type_map : major_type_t = 5uy

[@@CMacro]
let major_type_tagged : major_type_t = 6uy
