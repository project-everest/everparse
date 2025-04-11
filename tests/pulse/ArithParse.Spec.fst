module ArithParse.Spec
include ArithParse.Lib
open LowParse.Spec.Combinators
open LowParse.Spec.VCList
open LowParse.Spec.Recursive
open LowParse.Spec.Int

module U64 = FStar.UInt64
module U8 = FStar.UInt8

type expr =
| Plus of (l: list expr { List.Tot.length l < 254 })
| Minus of (expr & expr) // header 254
| Value of U64.t // header 255

let unit_as_uint64 = (x: U64.t { x == 0uL })
inline_for_extraction noextract [@@noextract_to "krml"]
let u_as_uint64 : unit_as_uint64 = 0uL

let header_rhs (lhs: U8.t) = if lhs = 255uy then U64.t else unit_as_uint64

let header = dtuple2 U8.t header_rhs

let parse_header_rhs_kind : parser_kind =
  strong_parser_kind 0 8 None

let parse_header_rhs (lhs: U8.t) : Tot (parser parse_header_rhs_kind (header_rhs lhs)) =
      if lhs = 255uy
      then weaken parse_header_rhs_kind parse_u64
      else weaken parse_header_rhs_kind (parse_ret u_as_uint64)

let tot_parse_header_rhs (lhs: U8.t) : Tot (tot_parser parse_header_rhs_kind (header_rhs lhs)) =
      if lhs = 255uy
      then tot_weaken parse_header_rhs_kind tot_parse_u64
      else tot_weaken parse_header_rhs_kind (tot_parse_ret u_as_uint64)

let tot_parse_header : tot_parser _ header =
  tot_parse_dtuple2 tot_parse_u8 tot_parse_header_rhs    

let parse_header_kind = and_then_kind parse_u8_kind parse_header_rhs_kind

let parse_header : parser parse_header_kind header =
  parse_dtuple2 parse_u8 parse_header_rhs    

let parse_header_eq () : Lemma (forall x . parse parse_header x == parse tot_parse_header x) =
  let prf (x: bytes) : Lemma
    (parse parse_header x == parse tot_parse_header x)
  = parse_dtuple2_eq parse_u8 parse_header_rhs x;
    ()
  in
  Classical.forall_intro prf

let count_payload (h: header) : Tot nat =
  match h with
  | (| 255uy, _ |) -> 0
  | (| 254uy, _ |) -> 2
  | (| v, _ |) -> U8.v v

let synth_expr (hp: parse_recursive_alt_t expr header count_payload) : Tot expr =
  let (| h, p |) = hp in
  match h with
  | (| 255uy, v |) -> Value v
  | (| 254uy, _ |) -> let [v1; v2] = p in Minus (v1, v2)
  | _ -> Plus p

let parse_expr_kind = parse_recursive_kind parse_header_kind

#push-options "--ifuel 4"
#restart-solver
let synth_expr_injective () : Lemma (synth_injective synth_expr) = ()
#pop-options

let parse_expr_param : parse_recursive_param = {
  t = expr;
  header = header;
  parse_header_kind = parse_header_kind;
  parse_header = tot_parse_header;
  count = count_payload;
  synth_ = synth_expr;
  synth_inj = synth_expr_injective ();
}

let tot_parse_expr = parse_recursive parse_expr_param

let tot_serialize_header_rhs (lhs: U8.t) : tot_serializer (tot_parse_header_rhs lhs) =
  if lhs = 255uy
  then tot_serialize_weaken parse_header_rhs_kind tot_serialize_u64
  else tot_serialize_weaken parse_header_rhs_kind (tot_serialize_ret u_as_uint64 (fun _ -> ()))

let tot_serialize_header : tot_serializer tot_parse_header =
  tot_serialize_dtuple2 tot_serialize_u8 tot_serialize_header_rhs

let serialize_header_rhs (lhs: U8.t) : serializer (parse_header_rhs lhs) =
  if lhs = 255uy
  then serialize_weaken parse_header_rhs_kind serialize_u64
  else serialize_weaken parse_header_rhs_kind (serialize_ret u_as_uint64 (fun _ -> ()))

let serialize_header : serializer parse_header =
  serialize_dtuple2 serialize_u8 serialize_header_rhs

let synth_expr_recip
  (x: expr)
: Tot (parse_recursive_alt_t expr header count_payload)
= match x with
  | Value v -> (| (| 255uy, v |), [] |)
  | Minus (v1, v2) -> (| (| 254uy, u_as_uint64 |), [v1; v2] |)
  | Plus p -> (| (| U8.uint_to_t (List.Tot.length p), u_as_uint64 |), p |)

let synth_expr_inverse () : Lemma (synth_inverse synth_expr synth_expr_recip) = ()

let rec level (x: expr) : Tot nat =
  match x with
  | Value _ -> 0
  | Minus (v1, v2) -> 1 + level v1 + level v2
  | Plus l -> 1 + wf_list_sum l level

let level' (x: expr) : Tot nat =
  match x with
  | Value _ -> 0
  | Minus (v1, v2) -> 1 + level v1 + level v2
  | Plus l -> 1 + list_sum level l

let level_eq (x: expr) : Lemma
  (level x == level' x)
= match x with
  | Plus l ->
    assert_norm (level (Plus l) == 1 + wf_list_sum l level);
    wf_list_sum_eq level l
  | _ -> ()

let level_correct (x: expr) (n: nat) : Lemma
  (requires has_level level n x)
  (ensures (list_has_pred_level level n (dsnd (synth_expr_recip x))))
  (decreases x)
= level_eq x;
  match x with
  | Plus l ->
    forall_list_intro (has_level level (n - 1)) l (fun x ->
      list_sum_memP level l x
    )
  | _ -> ()

let serialize_expr_param : serialize_recursive_param parse_expr_param = {
  serialize_header = tot_serialize_header;
  synth_recip = synth_expr_recip;
  synth_inv = synth_expr_inverse ();
  level = level;
  level_correct = level_correct
}

let tot_serialize_expr : tot_serializer tot_parse_expr = serialize_recursive serialize_expr_param
