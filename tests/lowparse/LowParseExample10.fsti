module LowParseExample10

module LPB = LowParse.SLow.Bytes
module LPI = LowParse.SLow.Int
module LL = LowParse.Low.Base
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module BY = LowParse.Bytes32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

(* Ideal output for something like:

struct {
  opaque msg_type[3];
  (if msg_type=abcdef then uint32 else uint16) contents;
} t;

*)

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
let parse_t_kind : LPB.parser_kind = LPB.strong_parser_kind 5 7 (Some LPB.ParserKindMetadataTotal)

val parse_t: LPB.parser parse_t_kind t

val serialize_t: LPB.serializer parse_t

val parse32_t : LPB.parser32 parse_t

val serialize32_t : LPB.serializer32 serialize_t

val size32_t : LPB.size32 serialize_t

val validate_t : LL.validator parse_t

val jump_t : LL.jumper parse_t

val t_elim (h: HS.mem) (input: LL.slice) (pos: U32.t) : Lemma
  (requires (LL.valid parse_t h input pos))
  (ensures (
    LL.valid (LPB.parse_flbytes 3) h input pos /\ (
    let x = LL.contents parse_t h input pos in
    let y = LL.contents (LPB.parse_flbytes 3) h input pos in
    y == (match x with
    | HelloRetryRequest _ -> msg_type_HelloRetryRequest
    | Other m -> m.msg_type
  ))))

val t_test_HelloRetryRequest (input: LL.slice) (pos: U32.t) : HST.Stack bool
  (requires (fun h -> LL.valid parse_t h input pos))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    (res == true <==> HelloRetryRequest? (LL.contents parse_t h input pos))
  ))

let clens_HelloRetryRequest : LL.clens t U32.t = {
  LL.clens_cond = (fun x -> HelloRetryRequest? x);
  LL.clens_get = (fun x -> (match x with HelloRetryRequest y -> y) <: Ghost U32.t (requires (HelloRetryRequest? x)) (ensures (fun _ -> True)));
}

val t_gaccessor_HelloRetryRequest: LL.gaccessor parse_t LPI.parse_u32 clens_HelloRetryRequest

val t_accessor_HelloRetryRequest: LL.accessor t_gaccessor_HelloRetryRequest

let clens_other : LL.clens t U16.t = {
  LL.clens_cond = (fun x -> Other? x);
  LL.clens_get = (fun x -> (match x with Other m -> m.contents) <: Ghost U16.t (requires (Other? x)) (ensures (fun _ -> True)));
}

val t_gaccessor_other: LL.gaccessor parse_t LPI.parse_u16 clens_other

val t_accessor_other: LL.accessor t_gaccessor_other

val t_intro_HelloRetryRequest (h: HS.mem) (input: LL.slice) (pos: U32.t) : Lemma
  (requires (
    LL.valid (LPB.parse_flbytes 3) h input pos /\ (
    let x = LL.contents (LPB.parse_flbytes 3) h input pos in
    let pos1 = LL.get_valid_pos (LPB.parse_flbytes 3) h input pos in
    x == msg_type_HelloRetryRequest /\
    LL.valid LPI.parse_u32 h input pos1
  )))
  (ensures (
    let pos1 = LL.get_valid_pos (LPB.parse_flbytes 3) h input pos in
    LL.valid_content_pos parse_t h input pos (HelloRetryRequest (LL.contents LPI.parse_u32 h input pos1)) (LL.get_valid_pos LPI.parse_u32 h input pos1)
  ))

val t_intro_other (h: HS.mem) (input: LL.slice) (pos: U32.t) : Lemma
  (requires (
    LL.valid (LPB.parse_flbytes 3) h input pos /\ (
    let x = LL.contents (LPB.parse_flbytes 3) h input pos in
    let pos1 = LL.get_valid_pos (LPB.parse_flbytes 3) h input pos in
    x =!= msg_type_HelloRetryRequest /\
    LL.valid LPI.parse_u16 h input pos1
  )))
  (ensures (
    let x = LL.contents (LPB.parse_flbytes 3) h input pos in
    let pos1 = LL.get_valid_pos (LPB.parse_flbytes 3) h input pos in
    LL.valid_content_pos parse_t h input pos (Other ({ msg_type = x; contents = (LL.contents LPI.parse_u16 h input pos1) })) (LL.get_valid_pos LPI.parse_u16 h input pos1)
  ))

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
