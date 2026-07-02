module LowParseExample10.Aux

include LowParse.Spec.Combinators
include LowParse.Spec.Int
include LowParse.Spec.IfThenElse

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

(* Use ((U8.t & U8.t) & U8.t) instead of flbytes 3 *)

inline_for_extraction
let msg_type = (U8.t & U8.t) & U8.t

inline_for_extraction
let msg_type_HelloRetryRequest : msg_type = ((0xABuy, 0xCDuy), 0xEFuy)

inline_for_extraction
let msg_type_eq (x y: msg_type) : Tot bool =
  let ((a1, b1), c1) = x in
  let ((a2, b2), c2) = y in
  a1 = a2 && b1 = b2 && c1 = c2

type msg_type_other = (m: msg_type { msg_type_eq m msg_type_HelloRetryRequest == false })

noeq
type t_other = {
  msg_type: msg_type_other;
  contents: U16.t;
}

noeq
type t =
  | HelloRetryRequest of U32.t
  | Other of t_other

inline_for_extraction
let t_tag_cond (x: msg_type) : Tot bool =
  msg_type_eq x msg_type_HelloRetryRequest

inline_for_extraction
let t_payload (b: bool) : Tot Type =
  if b then U32.t else U16.t

inline_for_extraction
let parse_t_payload (b: bool) : Tot (k: parser_kind & parser k (t_payload b)) =
  if b then (| _ , parse_u32 |) else (| _, parse_u16 |)

inline_for_extraction
let t_synth (x: msg_type) (y: t_payload (t_tag_cond x)) : Tot t =
  if t_tag_cond x
  then HelloRetryRequest y
  else Other ({ msg_type = x; contents = y })

let parse_msg_type : parser _ msg_type =
  parse_u8 `nondep_then` parse_u8 `nondep_then` parse_u8

inline_for_extraction
noextract
let parse_t_param : parse_ifthenelse_param = {
  parse_ifthenelse_tag_kind = _;
  parse_ifthenelse_tag_t = _;
  parse_ifthenelse_tag_parser = parse_msg_type;
  parse_ifthenelse_tag_cond = t_tag_cond;
  parse_ifthenelse_payload_t = t_payload;
  parse_ifthenelse_payload_parser = parse_t_payload;
  parse_ifthenelse_t = _;
  parse_ifthenelse_synth = t_synth;
  parse_ifthenelse_synth_injective = (fun t1 x1 t2 x2 -> ());
}

let parse_t : parser _ t = parse_ifthenelse parse_t_param
