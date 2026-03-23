module LowParseExample10.Aux

(* Spec + ifthenelse definition for Example10, as a regular F* module.
   Ported from tests/lowparse/LowParseExample10.fst + .fsti *)

include LowParse.Spec.Combinators
include LowParse.Spec.Bytes
include LowParse.Spec.Int
include LowParse.Spec.IfThenElse

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module BY = LowParse.Bytes32

type msg_type = BY.lbytes 3

let msg_type_HelloRetryRequest' : BY.bytes = BY.bytes_of_hex "abcdef"

let msg_type_HelloRetryRequest : msg_type =
  assume (BY.length msg_type_HelloRetryRequest' == 3);
  msg_type_HelloRetryRequest'

type msg_type_other = (msg_type: msg_type { msg_type <> msg_type_HelloRetryRequest } )

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
  x = msg_type_HelloRetryRequest

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

inline_for_extraction
noextract
let parse_t_param = {
  parse_ifthenelse_tag_kind = _;
  parse_ifthenelse_tag_t = _;
  parse_ifthenelse_tag_parser = parse_flbytes 3;
  parse_ifthenelse_tag_cond = t_tag_cond;
  parse_ifthenelse_payload_t = t_payload;
  parse_ifthenelse_payload_parser = parse_t_payload;
  parse_ifthenelse_t = _;
  parse_ifthenelse_synth = t_synth;
  parse_ifthenelse_synth_injective = (fun t1 x1 t2 x2 -> ());
}

let parse_t : parser _ t = parse_ifthenelse parse_t_param

inline_for_extraction
let serialize_t_payload (b: bool) : Tot (serializer (dsnd (parse_t_param.parse_ifthenelse_payload_parser b))) =
  if b then serialize_u32 else serialize_u16

inline_for_extraction
let t_synth_recip (x: t) : GTot (t: msg_type & (t_payload (t_tag_cond t))) =
  match x with
  | HelloRetryRequest y -> (| msg_type_HelloRetryRequest, y |)
  | Other m -> (| m.msg_type, m.contents |)

inline_for_extraction
noextract
let serialize_t_param : serialize_ifthenelse_param parse_t_param = {
  serialize_ifthenelse_tag_serializer = serialize_flbytes 3;
  serialize_ifthenelse_payload_serializer = serialize_t_payload;
  serialize_ifthenelse_synth_recip = t_synth_recip;
  serialize_ifthenelse_synth_inverse = (fun x -> ());
}

let serialize_t : serializer parse_t = serialize_ifthenelse serialize_t_param
