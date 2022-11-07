module LowParse.Tot.DER
include LowParse.Spec.DER
include LowParse.Tot.BoundedInt

module U32 = FStar.UInt32
module U8 = FStar.UInt8

let parse_der_length_payload32_bare
  (x: U8.t { der_length_payload_size_of_tag x <= 4 } )
  (input: bytes)
: Pure (option ((refine_with_tag tag_of_der_length32 x) * consumed_length input))
    (requires True)
    (ensures (fun y ->
      y == parse (parse_der_length_payload32 x) input
    ))
=
    parse_der_length_payload32_unfold x input;
    if U8.v x < 128
    then Some (FStar.Int.Cast.uint8_to_uint32 x, 0)
    else if x = 128uy || x = 255uy
    then None
    else if x = 129uy
    then
      match parse_u8 input with
      | None -> None
      | Some (z, consumed) ->
        if U8.v z < 128
        then None
        else Some (FStar.Int.Cast.uint8_to_uint32 z, consumed)
    else
      let len : nat = U8.v x - 128 in
      let _ = parse_bounded_integer_spec len input in
      let res : option (bounded_integer len & consumed_length input) = (parse_bounded_integer len) input in
      match res with
      | None -> None
      | Some (z, consumed) ->
        if U32.v z >= pow2 (8 `op_Multiply` (len - 1))
        then Some ((z <: refine_with_tag tag_of_der_length32 x), consumed)
        else None

let parse_bounded_der_length32_bare
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
  (input: bytes)
: Pure (option (bounded_int32 min max & consumed_length input))
    (requires True)
    (ensures (fun y ->
      y == parse (parse_bounded_der_length32 min max) input
    ))
=
   parse_bounded_der_length32_unfold min max input;
   match parse_u8 input with
   | None -> None
   | Some (x, consumed_x) ->
     let len = der_length_payload_size_of_tag x in
     if der_length_payload_size min <= len && len <= der_length_payload_size max then
      let input' = Seq.slice input consumed_x (Seq.length input) in
      match (parse_der_length_payload32_bare x) input' with
      | Some (y, consumed_y) ->
        if min <= U32.v y && U32.v y <= max
        then Some (y, consumed_x + consumed_y)
        else None
      | None -> None
     else
       None

val parse_bounded_der_length32
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
: Tot (parser (parse_bounded_der_length32_kind min max) (bounded_int32 min max))

let parse_bounded_der_length32
  min max
=
  parser_kind_prop_ext (parse_bounded_der_length32_kind min max) (parse_bounded_der_length32 min max) (parse_bounded_der_length32_bare min max);
  parse_bounded_der_length32_bare min max

val serialize_bounded_der_length32
  (min: der_length_t)
  (max: der_length_t { min <= max /\ max < 4294967296 })
: Tot (serializer #(parse_bounded_der_length32_kind min max) (parse_bounded_der_length32 min max))

let serialize_bounded_der_length32
  min max
= serialize_ext
    _
    (serialize_bounded_der_length32 min max)
    _
