module LowParse.Low.Int32le

(* LowParse implementation module for 32 bits little endian integers *)

include LowParse.Low.Combinators
include LowParse.Spec.Int32le

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

inline_for_extraction
let read_int32le : leaf_reader parse_int32le
= make_total_constant_size_reader 4 4ul decode_int32le (decode_int32le_total_constant ()) (fun #rrel #rel b pos ->
    let h = HST.get () in
    [@inline_let] let _ = decode_int32le_eq (Seq.slice (B.as_seq h b) (U32.v pos) (U32.v pos + 4)) in
    let r0 = B.index b pos in
    let r1 = B.index b (pos `U32.add` 1ul) in
    let r2 = B.index b (pos `U32.add` 2ul) in
    let r3 = B.index b (pos `U32.add` 3ul) in
    Cast.uint8_to_uint32 r0 `U32.add` (256ul `U32.mul` (Cast.uint8_to_uint32 r1 `U32.add` (256ul `U32.mul` (Cast.uint8_to_uint32 r2 `U32.add` (256ul `U32.mul` Cast.uint8_to_uint32 r3)))))
  )

inline_for_extraction
let validate_int32le : validator parse_int32le
= validate_total_constant_size parse_int32le 4uL ()
