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
noextract
let validate_bounded_integer_le
  (i: integer_size) // must be a constant
: Tot (validator (parse_bounded_integer_le i))
= validate_total_constant_size (parse_bounded_integer_le i) (U32.uint_to_t i) ()

inline_for_extraction
noextract
let jump_bounded_integer
  (i: integer_size) // must be a constant
: Tot (jumper (parse_bounded_integer i))
= jump_constant_size (parse_bounded_integer i) (U32.uint_to_t i) ()

inline_for_extraction
noextract
let jump_bounded_integer_le
  (i: integer_size) // must be a constant
: Tot (jumper (parse_bounded_integer_le i))
= jump_constant_size (parse_bounded_integer_le i) (U32.uint_to_t i) ()

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

val write_bounded_int32_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (leaf_writer_strong (serialize_bounded_int32 (U32.v min32) (U32.v max32)))

val write_bounded_int32_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (leaf_writer_strong (serialize_bounded_int32 (U32.v min32) (U32.v max32)))

val write_bounded_int32_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (leaf_writer_strong (serialize_bounded_int32 (U32.v min32) (U32.v max32)))

val write_bounded_int32_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (leaf_writer_strong (serialize_bounded_int32 (U32.v min32) (U32.v max32)))

inline_for_extraction
let write_bounded_int32
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (leaf_writer_strong (serialize_bounded_int32 (U32.v min32) (U32.v max32)))
= fun input #rrel #rel out pos -> (
  if max32 `U32.lt` 256ul
  then write_bounded_int32_1 min32 max32 input out pos
  else if max32 `U32.lt` 65536ul
  then write_bounded_int32_2 min32 max32 input out pos
  else if max32 `U32.lt` 16777216ul
  then write_bounded_int32_3 min32 max32 input out pos
  else write_bounded_int32_4 min32 max32 input out pos
  )

val read_bounded_int32_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (leaf_reader (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val read_bounded_int32_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (leaf_reader (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val read_bounded_int32_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (leaf_reader (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val read_bounded_int32_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (leaf_reader (parse_bounded_int32 (U32.v min32) (U32.v max32)))

inline_for_extraction
let read_bounded_int32
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (leaf_reader (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= fun #rrel #rel sl pos -> (
  if max32 `U32.lt` 256ul
  then read_bounded_int32_1 min32 max32 sl pos
  else if max32 `U32.lt` 65536ul
  then read_bounded_int32_2 min32 max32 sl pos
  else if max32 `U32.lt` 16777216ul
  then read_bounded_int32_3 min32 max32 sl pos
  else read_bounded_int32_4 min32 max32 sl pos
  )

val validate_bounded_int32_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (validator (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val validate_bounded_int32_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (validator (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val validate_bounded_int32_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (validator (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val validate_bounded_int32_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (validator (parse_bounded_int32 (U32.v min32) (U32.v max32)))

inline_for_extraction
let validate_bounded_int32
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (validator (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= fun #rrel #rel sl pos -> (
  if max32 `U32.lt` 256ul
  then validate_bounded_int32_1 min32 max32 sl pos
  else if max32 `U32.lt` 65536ul
  then validate_bounded_int32_2 min32 max32 sl pos
  else if max32 `U32.lt` 16777216ul
  then validate_bounded_int32_3 min32 max32 sl pos
  else validate_bounded_int32_4 min32 max32 sl pos
  )

val jump_bounded_int32_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val jump_bounded_int32_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val jump_bounded_int32_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))

val jump_bounded_int32_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))

inline_for_extraction
let jump_bounded_int32
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (jumper (parse_bounded_int32 (U32.v min32) (U32.v max32)))
= fun #rrel #rel sl pos -> (
  if max32 `U32.lt` 256ul
  then jump_bounded_int32_1 min32 max32 sl pos
  else if max32 `U32.lt` 65536ul
  then jump_bounded_int32_2 min32 max32 sl pos
  else if max32 `U32.lt` 16777216ul
  then jump_bounded_int32_3 min32 max32 sl pos
  else jump_bounded_int32_4 min32 max32 sl pos
  )

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
val read_bounded_integer_le_3 : leaf_reader (parse_bounded_integer_le 3)

inline_for_extraction
val read_bounded_integer_le_4 : leaf_reader (parse_bounded_integer_le 4)

inline_for_extraction
noextract
let read_bounded_integer_le
  (i: integer_size)
: Tot (leaf_reader (parse_bounded_integer_le i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> read_bounded_integer_le_1
  | 2 -> read_bounded_integer_le_2
  | 3 -> read_bounded_integer_le_3
  | 4 -> read_bounded_integer_le_4

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
val serialize32_bounded_integer_le_3 : serializer32 (serialize_bounded_integer_le 3)

inline_for_extraction
val write_bounded_integer_le_3 : leaf_writer_strong (serialize_bounded_integer_le 3)

inline_for_extraction
val serialize32_bounded_integer_le_4 : serializer32 (serialize_bounded_integer_le 4)

inline_for_extraction
val write_bounded_integer_le_4 : leaf_writer_strong (serialize_bounded_integer_le 4)

inline_for_extraction
noextract
let write_bounded_integer_le
  (i: integer_size)
: Tot (leaf_writer_strong (serialize_bounded_integer_le i))
= [@inline_let]
  let _ = integer_size_values i in
  match i with
  | 1 -> write_bounded_integer_le_1
  | 2 -> write_bounded_integer_le_2
  | 3 -> write_bounded_integer_le_3
  | 4 -> write_bounded_integer_le_4

inline_for_extraction
val write_u16_le : leaf_writer_strong serialize_u16_le

inline_for_extraction
val write_u32_le : leaf_writer_strong serialize_u32_le


val validate_bounded_int32_le_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (validator (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val validate_bounded_int32_le_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (validator (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val validate_bounded_int32_le_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (validator (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val validate_bounded_int32_le_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (validator (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

inline_for_extraction
let validate_bounded_int32_le
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (validator (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= fun #rrel #rel sl pos -> (
  if max32 `U32.lt` 256ul
  then validate_bounded_int32_le_1 min32 max32 sl pos
  else if max32 `U32.lt` 65536ul
  then validate_bounded_int32_le_2 min32 max32 sl pos
  else if max32 `U32.lt` 16777216ul
  then validate_bounded_int32_le_3 min32 max32 sl pos
  else validate_bounded_int32_le_4 min32 max32 sl pos
  )

val jump_bounded_int32_le_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val jump_bounded_int32_le_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val jump_bounded_int32_le_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val jump_bounded_int32_le_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

inline_for_extraction
let jump_bounded_int32_le
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (jumper (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= fun #rrel #rel sl pos -> (
  if max32 `U32.lt` 256ul
  then jump_bounded_int32_le_1 min32 max32 sl pos
  else if max32 `U32.lt` 65536ul
  then jump_bounded_int32_le_2 min32 max32 sl pos
  else if max32 `U32.lt` 16777216ul
  then jump_bounded_int32_le_3 min32 max32 sl pos
  else jump_bounded_int32_le_4 min32 max32 sl pos
  )

val write_bounded_int32_le_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (leaf_writer_strong (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))

val write_bounded_int32_le_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (leaf_writer_strong (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))

val write_bounded_int32_le_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (leaf_writer_strong (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))

val write_bounded_int32_le_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (leaf_writer_strong (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))

inline_for_extraction
let write_bounded_int32_le
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (leaf_writer_strong (serialize_bounded_int32_le (U32.v min32) (U32.v max32)))
= fun input #rrel #rel out pos -> (
  if max32 `U32.lt` 256ul
  then write_bounded_int32_le_1 min32 max32 input out pos
  else if max32 `U32.lt` 65536ul
  then write_bounded_int32_le_2 min32 max32 input out pos
  else if max32 `U32.lt` 16777216ul
  then write_bounded_int32_le_3 min32 max32 input out pos
  else write_bounded_int32_le_4 min32 max32 input out pos
  )

val read_bounded_int32_le_1
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 256 })
: Tot (leaf_reader (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val read_bounded_int32_le_2
  (min32: U32.t)
  (max32: U32.t { 256 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 65536 })
: Tot (leaf_reader (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val read_bounded_int32_le_3
  (min32: U32.t)
  (max32: U32.t { 65536 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 16777216 })
: Tot (leaf_reader (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

val read_bounded_int32_le_4
  (min32: U32.t)
  (max32: U32.t { 16777216 <= U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (leaf_reader (parse_bounded_int32_le (U32.v min32) (U32.v max32)))

inline_for_extraction
let read_bounded_int32_le
  (min32: U32.t)
  (max32: U32.t { 0 < U32.v max32 /\ U32.v min32 <= U32.v max32 /\ U32.v max32 < 4294967296 })
: Tot (leaf_reader (parse_bounded_int32_le (U32.v min32) (U32.v max32)))
= fun #rrel #rel sl pos -> (
  if max32 `U32.lt` 256ul
  then read_bounded_int32_le_1 min32 max32 sl pos
  else if max32 `U32.lt` 65536ul
  then read_bounded_int32_le_2 min32 max32 sl pos
  else if max32 `U32.lt` 16777216ul
  then read_bounded_int32_le_3 min32 max32 sl pos
  else read_bounded_int32_le_4 min32 max32 sl pos
  )

val validate_bounded_int32_le_fixed_size
  (min32: U32.t)
  (max32: U32.t { U32.v min32 <= U32.v max32 })
: Tot (validator (parse_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32)))

inline_for_extraction
let jump_bounded_int32_le_fixed_size
  (min32: U32.t)
  (max32: U32.t { U32.v min32 <= U32.v max32 })
: Tot (jumper (parse_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32)))
= jump_constant_size (parse_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32)) 4ul ()

val read_bounded_int32_le_fixed_size
  (min32: U32.t)
  (max32: U32.t { U32.v min32 <= U32.v max32 })
: Tot (leaf_reader (parse_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32)))

val write_bounded_int32_le_fixed_size
  (min32: U32.t)
  (max32: U32.t { U32.v min32 <= U32.v max32 })
: Tot (leaf_writer_strong (serialize_bounded_int32_le_fixed_size (U32.v min32) (U32.v max32)))
