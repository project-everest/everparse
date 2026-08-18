module ArithParse.Spec
include ArithParse.Lib
open LowParse.Spec.Combinators
open LowParse.Spec.VCList
open LowParse.Spec.Recursive
open LowParse.Spec.Int

module U64 = FStar.UInt64
module U8 = FStar.UInt8

type expr =
| Plus: (n: nat) -> (sq: squash (n < 254)) -> (l: nlist n expr) -> expr
| Minus of (expr & expr) // header 254
| Value of U64.t // header 255

type header_rhs (lhs: U8.t) =
| HValue: (sq: squash (lhs = 255uy)) -> (v: U64.t) -> header_rhs lhs
| HUnit: squash (lhs <> 255uy) -> (v: unit) -> header_rhs lhs

let header = dtuple2 U8.t header_rhs

let parse_header_rhs_kind : parser_kind =
  strong_parser_kind 0 8 None

let parse_header_rhs (lhs: U8.t) : Tot (parser parse_header_rhs_kind (header_rhs lhs)) =
      if lhs = 255uy
      then weaken parse_header_rhs_kind (parse_synth ( parse_u64) (HValue ()))
      else weaken parse_header_rhs_kind (parse_synth (parse_empty) (HUnit ()))

let tot_parse_header_rhs (lhs: U8.t) : Tot (tot_parser parse_header_rhs_kind (header_rhs lhs)) =
      if lhs = 255uy
      then tot_weaken parse_header_rhs_kind (tot_parse_synth (tot_parse_u64) (HValue ()))
      else tot_weaken parse_header_rhs_kind (tot_parse_synth (tot_parse_empty) (HUnit ()))

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
  | (| 255uy, HValue _ v |) -> Value v
  | (| 254uy, _ |) -> let [v1; v2] = p in Minus (v1, v2)
  | (| n, _ |) -> Plus (U8.v n) () p

let parse_expr_kind = parse_recursive_kind parse_header_kind

#push-options "--ifuel 4"
#restart-solver
let synth_expr_injective () : Lemma (synth_injective synth_expr) = ()
#pop-options

[@@Pulse.Lib.Pervasives.pulse_unfold]
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

let parse_expr = parser_of_tot_parser tot_parse_expr

let parse_expr' =
  (parse_header `parse_dtuple2` spec_parse_recursive_payload parse_expr_param parse_expr) `parse_synth` synth_expr

let parse_expr_eq () : Lemma
  (forall b. parse parse_expr' b == parse parse_expr b)
= parse_header_eq ();
  parse_recursive_eq_gen parse_expr_param _ parse_header

let tot_serialize_header_rhs (lhs: U8.t) : tot_serializer (tot_parse_header_rhs lhs) =
  if lhs = 255uy
  then tot_serialize_weaken parse_header_rhs_kind (tot_serialize_synth _ (HValue ())  tot_serialize_u64 HValue?.v ())
  else tot_serialize_weaken parse_header_rhs_kind (tot_serialize_synth _ (HUnit ())  tot_serialize_empty HUnit?.v ())

let tot_serialize_header : tot_serializer tot_parse_header =
  tot_serialize_dtuple2 tot_serialize_u8 tot_serialize_header_rhs

let serialize_header_rhs (lhs: U8.t) : serializer (parse_header_rhs lhs) =
  if lhs = 255uy
  then serialize_weaken parse_header_rhs_kind (serialize_synth _ (HValue ())  serialize_u64 HValue?.v ())
  else serialize_weaken parse_header_rhs_kind (serialize_synth _ (HUnit ())  serialize_empty HUnit?.v ())

let serialize_header : serializer parse_header =
  serialize_dtuple2 serialize_u8 serialize_header_rhs

let synth_expr_recip
  (x: expr)
: Tot (parse_recursive_alt_t expr header count_payload)
= match x with
  | Value v -> (| (| 255uy, HValue () v |), [] |)
  | Minus (v1, v2) -> (| (| 254uy, HUnit () () |), [v1; v2] |)
  | Plus n _ p -> (| (| U8.uint_to_t n, HUnit () () |), p |)

let synth_expr_inverse () : Lemma (synth_inverse synth_expr synth_expr_recip) = ()

let rec level (x: expr) : Tot nat =
  match x with
  | Value _ -> 0
  | Minus (v1, v2) -> 1 + level v1 + level v2
  | Plus _ _ l -> 1 + wf_list_sum l level

let level' (x: expr) : Tot nat =
  match x with
  | Value _ -> 0
  | Minus (v1, v2) -> 1 + level v1 + level v2
  | Plus _ _ l -> 1 + list_sum level l

let level_eq (x: expr) : Lemma
  (level x == level' x)
= match x with
  | Plus _ _ l ->
    assert_norm (level (Plus _ _ l) == 1 + wf_list_sum l level);
    wf_list_sum_eq level l
  | _ -> ()

let level_correct (x: expr) (n: nat) : Lemma
  (requires has_level level n x)
  (ensures (list_has_pred_level level n (dsnd (synth_expr_recip x))))
  (decreases x)
= level_eq x;
  match x with
  | Plus _ _ l ->
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

let serialize_expr : serializer parse_expr = serializer_of_tot_serializer tot_serialize_expr

let serialize_expr' : serializer parse_expr' =
  serialize_synth
    _
    synth_expr
    (serialize_dtuple2
      serialize_header
      (spec_serialize_recursive_payload serialize_expr_param)
    )
    synth_expr_recip
    ()
