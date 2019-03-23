module LowParse.SLow.Int

module Aux = LowParse.SLow.Int.Aux
module Unique = LowParse.Spec.Int.Unique
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes

let parse32_u8 =
  (fun input ->
    [@inline_let]
    let _ = Unique.parse_u8_unique (B32.reveal input) in
    [@inline_let]
    let res : option (U8.t * U32.t) = Aux.parse32_u8 input in
    (res <: (res: option (U8.t * U32.t) { parser32_correct parse_u8 input res } ))
  )

let serialize32_u8
: serializer32 serialize_u8
= (fun (input: U8.t) ->
    [@inline_let]
    let _ = Unique.serialize_u8_unique input in
    [@inline_let]
    let res : bytes32 = Aux.serialize32_u8 input in
    (res <: (res: bytes32 { serializer32_correct #_ #_ #parse_u8 serialize_u8 input res } )))

let parse32_u16 =
  (fun input ->
    [@inline_let]
    let _ = Unique.parse_u16_unique (B32.reveal input) in
    [@inline_let]
    let res : option (U16.t * U32.t) = Aux.parse32_u16 input in
    (res <: (res: option (U16.t * U32.t) { parser32_correct parse_u16 input res } ))
  )

let serialize32_u16
: serializer32 serialize_u16
= (fun (input: U16.t) ->
    [@inline_let]
    let _ = Unique.serialize_u16_unique input in
    [@inline_let]
    let res : bytes32 = Aux.serialize32_u16 input in
    (res <: (res: bytes32 { serializer32_correct #_ #_ #parse_u16 serialize_u16 input res } )))

let parse32_u32 =
  (fun input ->
    [@inline_let]
    let _ = Unique.parse_u32_unique (B32.reveal input) in
    [@inline_let]
    let res : option (U32.t * U32.t) = Aux.parse32_u32 input in
    (res <: (res: option (U32.t * U32.t) { parser32_correct parse_u32 input res } ))
  )

let serialize32_u32
: serializer32 serialize_u32
= (fun (input: U32.t) ->
    [@inline_let]
    let _ = Unique.serialize_u32_unique input in
    [@inline_let]
    let res : bytes32 = Aux.serialize32_u32 input in
    (res <: (res: bytes32 { serializer32_correct #_ #_ #parse_u32 serialize_u32 input res } )))

