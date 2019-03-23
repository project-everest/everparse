module LowParseExample9

module LP = LowParse.Spec.Base
module LS = LowParse.SLow.Base
module LL = LowParse.Low.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

(* Ideal output for:

enum /*@open*/ {
  ka(0),
  kb(1),
  (255)
} kt;

struct {
  /*@implicit*/ kt k;
  select(k) {
    case ka: uint8;
    case kb: uint16;
    default: uint32;
  } x;
} tt;

*)

inline_for_extraction let kt_repr : eqtype = U8.t
inline_for_extraction let kt_repr_eq (x1 x2: kt_repr) : Tot bool = (x1 = x2)
let known_kt_repr (v:U8.t) : bool = v `kt_repr_eq` 0z || (v `kt_repr_eq` 1z || (false))

type kt =
  | Ka
  | Kb
  | Unknown_kt of (v:U8.t{not (known_kt_repr v)})

type tt =
  | Case_ka of U8.t
  | Case_kb of U16.t
  | Case_Unknown_kt: v:kt_repr{not (known_kt_repr v)} -> U32.t -> tt

inline_for_extraction let tag_of_tt (x:tt) : kt = match x with
  | Case_ka _ -> Ka
  | Case_kb _ -> Kb
  | Case_Unknown_kt v _ -> Unknown_kt v

inline_for_extraction
let t (k: kt) : Tot Type = (x: tt { tag_of_tt x == k } )

inline_for_extraction
let parse_t_kind : LP.parser_kind = LP.strong_parser_kind 1 4 (Some LP.ParserKindMetadataTotal)

val parse_t (k: kt) : Tot (LP.parser parse_t_kind (t k))

val serialize_t (k: kt) : Tot (LP.serializer (parse_t k))

val parse32_t (k: kt) : Tot (LS.parser32 (parse_t k))

val serialize32_t (k: kt) : Tot (LS.serializer32 (serialize_t k))

val size32_t (k: kt) : Tot (LS.size32 (serialize_t k))

val validate_t (k: kt) : Tot (LL.validator (parse_t k))

val jump_t (k: kt) : Tot (LL.jumper (parse_t k))

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
