module LowParseExample8

module LP = LowParse.Spec.Base
module LS = LowParse.SLow.Base
module LL = LowParse.Low.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16

type k_t : eqtype =
| Ka
| Kb

noeq
type t' =
| Ta of U8.t
| Tb of U16.t

inline_for_extraction
let key (x: t') : Tot k_t = match x with
| Ta _ -> Ka
| Tb _ -> Kb

inline_for_extraction
let t (k: k_t) : Tot Type = (x: t' { key x == k } )

inline_for_extraction
let parse_t_kind : LP.parser_kind = LP.strong_parser_kind 1 2 (Some LP.ParserKindMetadataTotal)

val parse_t (k: k_t) : Tot (LP.parser parse_t_kind (t k))

val serialize_t (k: k_t) : Tot (LP.serializer (parse_t k))

val parse32_t (k: k_t) : Tot (LS.parser32 (parse_t k))

val serialize32_t (k: k_t) : Tot (LS.serializer32 (serialize_t k))

val size32_t (k: k_t) : Tot (LS.size32 (serialize_t k))

val validate_t (k: k_t) : Tot (LL.validator (parse_t k))

val jump_t (k: k_t) : Tot (LL.jumper (parse_t k))

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
