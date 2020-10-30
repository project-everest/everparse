module LowParse.Spec.ListUpTo
include LowParse.Spec.Base

module L = FStar.List.Tot
module Seq = FStar.Seq

let negate_cond
  (#t: Type)
  (cond: (t -> Tot bool))
  (x: t)
: Tot bool
= not (cond x)

let refine_with_cond
  (#t: Type)
  (cond: (t -> Tot bool))
: Tot Type
= (x: t { cond x == true })

let parse_list_up_to_t
  (#t: Type)
  (cond: (t -> Tot bool))
: Tot Type
= list (refine_with_cond (negate_cond cond)) & refine_with_cond cond

inline_for_extraction
let parse_list_up_to_kind (k: parser_kind) : Tot (k' : parser_kind {k' `is_weaker_than` k }) = {
  parser_kind_low = k.parser_kind_low;
  parser_kind_high = None;
  parser_kind_subkind = k.parser_kind_subkind;
  parser_kind_metadata = None;
}

let consumes_if_not_cond
  (#k: parser_kind)
  (#t: Type)
  (cond: (t -> Tot bool))
  (p: parser k t)
: Tot Type
= 
    (b: bytes) ->
    (x: t) ->
    (consumed: consumed_length b) ->
    Lemma
    (requires (parse p b == Some (x, consumed) /\ (~ (cond x))))
    (ensures (consumed > 0))

val parse_list_up_to
  (#k: parser_kind)
  (#t: Type)
  (cond: (t -> Tot bool))
  (p: parser k t { k.parser_kind_subkind <> Some ParserConsumesAll })
  (prf: consumes_if_not_cond cond p)
: Tot (parser (parse_list_up_to_kind k) (parse_list_up_to_t cond))

val parse_list_up_to_eq
  (#k: parser_kind)
  (#t: Type)
  (cond: (t -> Tot bool))
  (p: parser k t { k.parser_kind_subkind <> Some ParserConsumesAll })
  (prf: consumes_if_not_cond cond p)
  (b: bytes)
: Lemma
  (parse (parse_list_up_to cond p prf) b == (
    match parse p b with
    | None -> None
    | Some (x, consumed) ->
      if cond x
      then Some (([], x), consumed)
      else begin match parse (parse_list_up_to cond p prf) (Seq.slice b consumed (Seq.length b)) with
      | None -> None
      | Some ((y, z), consumed') -> Some ((x::y, z), consumed + consumed')
      end
  ))

val serialize_list_up_to
  (#k: parser_kind)
  (#t: Type)
  (cond: (t -> Tot bool))
  (#p: parser k t)
  (prf: consumes_if_not_cond cond p)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
: Tot (serializer (parse_list_up_to cond p prf))

val serialize_list_up_to_eq
  (#k: parser_kind)
  (#t: Type)
  (cond: (t -> Tot bool))
  (#p: parser k t)
  (prf: consumes_if_not_cond cond p)
  (s: serializer p { k.parser_kind_subkind == Some ParserStrong })
  (xy: parse_list_up_to_t cond)
: Lemma
  (serialize (serialize_list_up_to cond prf s) xy == (
    let (l, z) = xy in
    match l with
    | [] -> serialize s z
    | x :: y -> serialize s x `Seq.append` serialize (serialize_list_up_to cond prf s) (y, z)
  ))
