module LowParseExample12

module LP = LowParse.Spec
module LS = LowParse.SLow
module LL = LowParse.Low

let parse_t' = LP.parse_vlgen 0 1023 (LP.parse_bounded_der_length32 0 1023) (LP.serialize_bounded_vlbytes 0 512)

let kind_eq : squash (parse_t_kind == LP.get_parser_kind parse_t') = _ by (FStar.Tactics.trefl ())

let parse_t = parse_t'

let serialize_t = LP.serialize_vlgen 0 1023 (LP.serialize_bounded_der_length32 0 1023) (LP.serialize_bounded_vlbytes 0 512)

let parse32_t =
  LS.parse32_vlgen 0 0ul 1023 1023ul (LS.parse32_bounded_der_length32 0 0ul 1023 1023ul) (LP.serialize_bounded_vlbytes 0 512) (LS.parse32_bounded_vlbytes 0 0ul 512 512ul)

let serialize32_t =
  LS.serialize32_vlgen 0 1023 (LS.serialize32_bounded_der_length32 0 1023) (LS.serialize32_bounded_vlbytes 0 512)

let size32_t =
  LS.size32_vlgen 0 1023 (LS.size32_bounded_der_length32 0 1023) (LS.size32_bounded_vlbytes 0 512)

let validate_t =
  LL.validate_vlgen 0 0ul 1023 1023ul (LL.validate_bounded_der_length32 0 0ul 1023 1023ul) (LL.read_bounded_der_length32 0 1023) (LP.serialize_bounded_vlbytes 0 512) (LL.validate_bounded_vlbytes 0 512)

let jump_t =
  LL.jump_vlgen 0 1023 (LL.jump_bounded_der_length32 0 1023) (LL.read_bounded_der_length32 0 1023) (LP.serialize_bounded_vlbytes 0 512) (LL.jump_bounded_vlbytes 0 512)

let main _ _ = C.EXIT_SUCCESS
