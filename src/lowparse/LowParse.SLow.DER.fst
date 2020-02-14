module LowParse.SLow.DER
include LowParse.Spec.DER
include LowParse.SLow.Combinators
include LowParse.SLow.Int // for parse32_u8
include LowParse.SLow.BoundedInt // for bounded_integer
open FStar.Mul

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Math = LowParse.Math
module B32 = LowParse.Bytes32
module Cast = FStar.Int.Cast

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"

#push-options "--z3rlimit 16"

inline_for_extraction
let parse32_der_length_payload32
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
: Tot (parser32 (parse_der_length_payload32 x))
= fun (input: bytes32) -> ((
    [@inline_let] let _ =
      parse_der_length_payload32_unfold x (B32.reveal input);
      assert_norm (pow2 (8 * 1) == 256);
      assert_norm (pow2 (8 * 2) == 65536);
      assert_norm (pow2 (8 * 3) == 16777216);
      assert_norm (pow2 (8 * 4) == 4294967296)
    in
    if x `U8.lt` 128uy
    then Some (Cast.uint8_to_uint32 x, 0ul)
    else if x = 128uy || x = 255uy
    then None
    else if x = 129uy
    then
      match parse32_u8 input with
      | None -> None
      | Some (z, consumed) ->
        if z `U8.lt` 128uy
        then None
        else Some ((Cast.uint8_to_uint32 z <: refine_with_tag tag_of_der_length32 x), consumed)
    else
      let len = x `U8.sub` 128uy in
      if len = 2uy
      then
        match parse32_bounded_integer 2 input with
        | None -> None
        | Some (y, consumed) ->
          if y `U32.lt `256ul
          then None
          else Some ((y <: refine_with_tag tag_of_der_length32 x), consumed)
      else if len = 3uy
      then
        match parse32_bounded_integer 3 input with
        | None -> None
        | Some (y, consumed) ->
          if y `U32.lt `65536ul
          then None
          else Some ((y <: refine_with_tag tag_of_der_length32 x), consumed)
      else
        match parse32_bounded_integer 4 input with
        | None -> None
        | Some (y, consumed) ->
          if y `U32.lt` 16777216ul
          then None
          else Some ((y <: refine_with_tag tag_of_der_length32 x), consumed)
  ) <: (res: _ { parser32_correct (parse_der_length_payload32 x) input res } ))

#push-options "--max_ifuel 2"

inline_for_extraction
let parse32_bounded_der_length32
  (vmin: der_length_t)
  (min: U32.t { U32.v min == vmin } )
  (vmax: der_length_t)
  (max: U32.t { U32.v max == vmax /\ U32.v min <= U32.v max } )
: Tot (
      parser32 (parse_bounded_der_length32 vmin vmax))
= [@inline_let] let _ = assert_norm (4294967296 <= der_length_max) in
  fun (input: bytes32) -> ((
    [@inline_let]
    let _ =
      parse_bounded_der_length32_unfold (U32.v min) (U32.v max) (B32.reveal input)
    in
    match parse32_u8 input with
    | None -> None
    | Some (x, consumed_x) ->
      let len = der_length_payload_size_of_tag8 x in
      let tg1 = (tag_of_der_length32_impl min)  in
      let l1 = der_length_payload_size_of_tag8 tg1 in
      let tg2 = (tag_of_der_length32_impl max) in
      let l2 = der_length_payload_size_of_tag8 tg2 in
      if len `U8.lt` l1 || l2 `U8.lt` len
      then None
      else begin
        let input' = B32.slice input consumed_x (B32.len input) in
        match parse32_der_length_payload32 x input' with
        | Some (y, consumed_y) ->
          if y `U32.lt` min || max `U32.lt` y
          then None
          else Some (y, consumed_x `U32.add` consumed_y)
        | None -> None
      end
  ) <: (res : _ { parser32_correct (parse_bounded_der_length32 (U32.v min) (U32.v max)) input res } ))

#pop-options

inline_for_extraction
let serialize32_bounded_der_length32
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
: Tot (serializer32 (serialize_bounded_der_length32 (vmin) (vmax)))
= fun (y' : bounded_int32 (vmin) (vmax)) -> ((
    [@inline_let]
    let _ = serialize_bounded_der_length32_unfold (vmin) (vmax) y' in
    let x = tag_of_der_length32_impl y' in
    let sx = B32.create 1ul x in
    if x `U8.lt` 128uy
    then sx
    else if x = 129uy
    then sx `B32.b32append` B32.create 1ul (Cast.uint32_to_uint8 y')
    else if x = 130uy
    then sx `B32.b32append` serialize32_bounded_integer_2 y'
    else if x = 131uy
    then sx `B32.b32append` serialize32_bounded_integer_3 y'
    else sx `B32.b32append` serialize32_bounded_integer_4 y'
  ) <: (res: _ { serializer32_correct (serialize_bounded_der_length32 (vmin) (vmax)) y' res } ))

inline_for_extraction
let size32_bounded_der_length32
  (vmin: der_length_t)
  (vmax: der_length_t { vmin <= vmax /\ vmax < 4294967296 } )
: Tot (size32 (serialize_bounded_der_length32 (vmin) (vmax)))
= fun (y' : bounded_int32 (vmin) (vmax)) -> ((
    [@inline_let]
    let _ = serialize_bounded_der_length32_size (vmin) (vmax) y' in
    if y' `U32.lt` 128ul
    then 1ul
    else if y' `U32.lt` 256ul
    then 2ul
    else if y' `U32.lt` 65536ul
    then 3ul
    else if y' `U32.lt` 16777216ul
    then 4ul
    else 5ul
  ) <: (res: _ { size32_postcond (serialize_bounded_der_length32 (vmin) (vmax)) y' res } ))

#pop-options
  
