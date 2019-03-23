module LowParseExample12

module LP = LowParse.Spec.Bytes
module LS = LowParse.SLow.Base
module LL = LowParse.Low.Base

inline_for_extraction
type t = LP.parse_bounded_vlbytes_t 0 512

inline_for_extraction
let parse_t_kind : LP.parser_kind = LP.strong_parser_kind 3 517 None

val parse_t : (LP.parser parse_t_kind t)

val serialize_t : (LP.serializer (parse_t))

val parse32_t : (LS.parser32 (parse_t))

val serialize32_t : (LS.serializer32 (serialize_t))

val size32_t : (LS.size32 (serialize_t))

val validate_t :  (LL.validator (parse_t))

val jump_t : (LL.jumper (parse_t))

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
