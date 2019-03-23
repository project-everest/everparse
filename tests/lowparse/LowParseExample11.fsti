module LowParseExample11

module LS = LowParse.SLow.Base
module LL = LowParse.Low.Base
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module L = FStar.List.Tot

inline_for_extraction
let slice = LowParse.Low.slice (LL.srel_of_buffer_srel (B.trivial_preorder _)) (LL.srel_of_buffer_srel (B.trivial_preorder _))

type elem = U32.t

type t = (l: list elem { let ln = L.length l in 10 <= ln /\ ln <= 1000 })

inline_for_extraction
let parse_t_kind : LL.parser_kind = LL.strong_parser_kind 11 5005 None

val parse_t: LL.parser parse_t_kind t

val serialize_t: LL.serializer parse_t

val parse32_t : LS.parser32 parse_t

val serialize32_t : LS.serializer32 serialize_t

val size32_t : LS.size32 serialize_t

val validate_t : LL.validator parse_t

val jump_t : LL.jumper parse_t

val read_6th: (sl: slice) -> (pos: U32.t) -> HST.Stack U32.t
  (requires (fun h -> LL.valid parse_t h sl pos))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == L.index (LL.contents parse_t h sl pos) 6
  ))

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
