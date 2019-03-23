module LowParse.SLow.BCVLI
include LowParse.Spec.BCVLI
include LowParse.SLow.Combinators // for make_total_constant_size_parser32
include LowParse.SLow.BoundedInt // for bounded_integer_le

module B32 = LowParse.Bytes32
module Seq = FStar.Seq
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

#push-options "--max_fuel 0"

let parse32_bcvli
: parser32 parse_bcvli
= fun input -> ((
    [@inline_let] let _ =
      parse_bcvli_eq (B32.reveal input)
    in
    match parse32_bounded_integer_le_1 input with
    | None -> None
    | Some (x32, consumed_x) ->
      if x32 `U32.lt` 253ul
      then Some (x32, consumed_x)
      else
        let input' = B32.slice input consumed_x (B32.len input) in
        if x32 = 253ul
        then
          match parse32_bounded_integer_le_2 input' with
          | None -> None
          | Some (y, consumed_y) ->
            if y `U32.lt` 253ul then None else Some (y, consumed_x `U32.add` consumed_y)
        else if x32 = 254ul
        then
          match parse32_bounded_integer_le_4 input' with
          | None -> None
          | Some (y, consumed_y) ->
            if y `U32.lt` 65536ul then None else Some (y, consumed_x `U32.add` consumed_y)
        else
          None
  ) <: (res: _ { parser32_correct parse_bcvli input res } ))

module U8 = FStar.UInt8

let serialize32_bcvli
: serializer32 serialize_bcvli
= fun x -> ((
    [@inline_let] let _ = serialize_bcvli_eq x in
    let c1 : bounded_integer 1 =
      if x `U32.lt` 253ul
      then x
      else if x `U32.lt` 65536ul
      then 253ul
      else 254ul
    in
    let s1 = serialize32_bounded_integer_le_1 c1 in
    if c1 `U32.lt` 253ul
    then s1
    else if c1 = 253ul
    then s1 `B32.append` serialize32_bounded_integer_le_2 x
    else s1 `B32.append` serialize32_bounded_integer_le_4 x
  ) <: (res: bytes32 { serializer32_correct' serialize_bcvli x res } ))

let size32_bcvli
: size32 serialize_bcvli
= fun x -> ((
    [@inline_let] let _ = serialize_bcvli_eq x in
    if x `U32.lt` 253ul
    then 1ul
    else if x `U32.lt` 65536ul
    then 3ul
    else 5ul
  ) <: (res: _ { size32_postcond serialize_bcvli x res } ))

#pop-options
