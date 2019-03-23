module LowParse.Low.BoundedInt
include LowParse.Spec.BoundedInt
include LowParse.Low.Base

module U32 = FStar.UInt32

(* bounded integers *)

inline_for_extraction
val read_bounded_integer_1 : unit -> Tot (leaf_reader (parse_bounded_integer 1))

inline_for_extraction
val read_bounded_integer_2 : unit -> Tot (leaf_reader (parse_bounded_integer 2))

inline_for_extraction
val read_bounded_integer_3 : unit -> Tot (leaf_reader (parse_bounded_integer 3))

inline_for_extraction
val read_bounded_integer_4 : unit -> Tot (leaf_reader (parse_bounded_integer 4))

inline_for_extraction
noextract
let read_bounded_integer
  (i: integer_size)
: Tot (leaf_reader (parse_bounded_integer i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> read_bounded_integer_1 ()
  | 2 -> read_bounded_integer_2 ()
  | 3 -> read_bounded_integer_3 ()
  | 4 -> read_bounded_integer_4 ()

inline_for_extraction
noextract
let validate_bounded_integer
  (i: integer_size) // must be a constant
: Tot (validator (parse_bounded_integer i))
= validate_total_constant_size (parse_bounded_integer i) (U32.uint_to_t i) ()

inline_for_extraction
val serialize32_bounded_integer_1 : unit -> Tot (serializer32 (serialize_bounded_integer 1))

inline_for_extraction
val serialize32_bounded_integer_2 : unit -> Tot (serializer32 (serialize_bounded_integer 2))

inline_for_extraction
val serialize32_bounded_integer_3 : unit -> Tot (serializer32 (serialize_bounded_integer 3))

inline_for_extraction
val serialize32_bounded_integer_4 : unit -> Tot (serializer32 (serialize_bounded_integer 4))

inline_for_extraction
let write_bounded_integer_1 () = leaf_writer_strong_of_serializer32 (serialize32_bounded_integer_1 ()) ()

inline_for_extraction
let write_bounded_integer_2 () = leaf_writer_strong_of_serializer32 (serialize32_bounded_integer_2 ()) ()

inline_for_extraction
let write_bounded_integer_3 () = leaf_writer_strong_of_serializer32 (serialize32_bounded_integer_3 ()) ()

inline_for_extraction
let write_bounded_integer_4 () = leaf_writer_strong_of_serializer32 (serialize32_bounded_integer_4 ()) ()

inline_for_extraction
noextract
let write_bounded_integer
  (i: integer_size)
: Tot (leaf_writer_strong (serialize_bounded_integer i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> write_bounded_integer_1 ()
  | 2 -> write_bounded_integer_2 ()
  | 3 -> write_bounded_integer_3 ()
  | 4 -> write_bounded_integer_4 ()

inline_for_extraction
let write_bounded_integer_1_weak (_ : unit) : Tot (leaf_writer_weak (serialize_bounded_integer 1)) =
  leaf_writer_weak_of_strong_constant_size (write_bounded_integer_1 ()) 1ul ()

inline_for_extraction
let write_bounded_integer_2_weak (_ : unit) : Tot (leaf_writer_weak (serialize_bounded_integer 2)) =
  leaf_writer_weak_of_strong_constant_size (write_bounded_integer_2 ()) 2ul ()

inline_for_extraction
let write_bounded_integer_3_weak (_ : unit) : Tot (leaf_writer_weak (serialize_bounded_integer 3)) =
  leaf_writer_weak_of_strong_constant_size (write_bounded_integer_3 ()) 3ul ()

inline_for_extraction
let write_bounded_integer_4_weak (_ : unit) : Tot (leaf_writer_weak (serialize_bounded_integer 4)) =
  leaf_writer_weak_of_strong_constant_size (write_bounded_integer_4 ()) 4ul ()

inline_for_extraction
noextract
let write_bounded_integer_weak
  (i: integer_size)
: Tot (leaf_writer_weak (serialize_bounded_integer i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> write_bounded_integer_1_weak ()
  | 2 -> write_bounded_integer_2_weak ()
  | 3 -> write_bounded_integer_3_weak ()
  | 4 -> write_bounded_integer_4_weak ()

inline_for_extraction
let validate_u16_le () : validator parse_u16_le =
  validate_total_constant_size parse_u16_le 2ul ()

inline_for_extraction
let validate_u32_le () : validator parse_u32_le =
  validate_total_constant_size parse_u32_le 4ul ()

inline_for_extraction
let jump_u16_le : jumper parse_u16_le =
  jump_constant_size parse_u16_le 2ul ()

inline_for_extraction
let jump_u32_le : jumper parse_u32_le =
  jump_constant_size parse_u32_le 4ul ()

inline_for_extraction
val read_bounded_integer_le_1 : leaf_reader (parse_bounded_integer_le 1)

inline_for_extraction
val read_bounded_integer_le_2 : leaf_reader (parse_bounded_integer_le 2)

inline_for_extraction
val read_bounded_integer_le_4 : leaf_reader (parse_bounded_integer_le 4)

inline_for_extraction
val read_u16_le : leaf_reader parse_u16_le

inline_for_extraction
val read_u32_le : leaf_reader parse_u32_le

inline_for_extraction
val serialize32_bounded_integer_le_1 : serializer32 (serialize_bounded_integer_le 1)

inline_for_extraction
val write_bounded_integer_le_1 : leaf_writer_strong (serialize_bounded_integer_le 1) 

inline_for_extraction
val serialize32_bounded_integer_le_2 : serializer32 (serialize_bounded_integer_le 2)

inline_for_extraction
val write_bounded_integer_le_2 : leaf_writer_strong (serialize_bounded_integer_le 2)

inline_for_extraction
val serialize32_bounded_integer_le_4 : serializer32 (serialize_bounded_integer_le 4)

inline_for_extraction
val write_bounded_integer_le_4 : leaf_writer_strong (serialize_bounded_integer_le 4)

inline_for_extraction
val write_u16_le : leaf_writer_strong serialize_u16_le

inline_for_extraction
val write_u32_le : leaf_writer_strong serialize_u32_le
