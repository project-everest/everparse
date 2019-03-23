module LowParse.MLow.Int
include LowParse.Spec.Int
include LowParse.MLow.Base

val read_u8: leaf_reader parse_u8

val read_u16: leaf_reader parse_u16

val read_u32: leaf_reader parse_u32

let validate_u8 () : validator parse_u8 =
  validate_total_constant_size parse_u8 1ul ()

let validate_u16 () : validator parse_u16 =
  validate_total_constant_size parse_u16 2ul ()

let validate_u32 () : validator parse_u32 =
  validate_total_constant_size parse_u32 4ul ()

let jump_u8 : jumper parse_u8 =
  jump_constant_size parse_u8 1ul ()

let jump_u16 : jumper parse_u16 =
  jump_constant_size parse_u16 2ul ()

let jump_u32 : jumper parse_u32 =
  jump_constant_size parse_u32 4ul ()

val write_u8 : leaf_writer_strong serialize_u8

(*
let write_u8_weak : leaf_writer_weak serialize_u8 =
  leaf_writer_weak_of_strong_constant_size write_u8 1ul ()
*)

val write_u16 : leaf_writer_strong serialize_u16

(*
let write_u16_weak : leaf_writer_weak serialize_u16 =
  leaf_writer_weak_of_strong_constant_size write_u16 2ul ()
*)

val write_u32 : leaf_writer_strong serialize_u32

(*
let write_u32_weak : leaf_writer_weak serialize_u32 =
  leaf_writer_weak_of_strong_constant_size write_u32 4ul ()
*)
