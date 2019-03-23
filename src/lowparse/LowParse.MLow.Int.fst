module LowParse.MLow.Int
include LowParse.Spec.Int
include LowParse.MLow.Base

module Aux = LowParse.MLow.Int.Aux
module Unique = LowParse.Spec.Int.Unique
module B = LowStar.Monotonic.Buffer

let read_u8 = admit ()

let read_u16 = admit ()

let read_u32 = admit ()

inline_for_extraction
let serialize32_u8 : serializer32 serialize_u8 = fun v (#rrel #rel: B.srel byte) out pos ->
  [@inline_let] let _ = Unique.serialize_u8_unique v in
  Aux.serialize32_u8 v out pos

let write_u8 = leaf_writer_strong_of_serializer32 serialize32_u8 ()

(*
let write_u8_weak : leaf_writer_weak serialize_u8 =
  leaf_writer_weak_of_strong_constant_size write_u8 1ul ()
*)

inline_for_extraction
let serialize32_u16 : serializer32 serialize_u16 = fun v (#rrel #rel: B.srel byte) out pos ->
  [@inline_let] let _ = Unique.serialize_u16_unique v in
  Aux.serialize32_u16 v out pos

let write_u16 = leaf_writer_strong_of_serializer32 serialize32_u16 ()

(*
let write_u16_weak : leaf_writer_weak serialize_u16 =
  leaf_writer_weak_of_strong_constant_size write_u16 2ul ()
*)

let write_u32 : leaf_writer_strong serialize_u32 = admit ()

(*
let write_u32_weak : leaf_writer_weak serialize_u32 =
  leaf_writer_weak_of_strong_constant_size write_u32 4ul ()
*)
