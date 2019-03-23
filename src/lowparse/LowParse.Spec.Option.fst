module LowParse.Spec.Option
include LowParse.Spec.Base

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

let parse_option_kind (k: parser_kind) : Tot parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = k.parser_kind_high;
  parser_kind_subkind = None;
}

let parse_option_bare (#k: parser_kind) (#t: Type) (p: parser k t) : Tot (bare_parser (option t)) =
  fun (input: bytes) ->
  match parse p input with
  | Some (data, consumed) -> Some (Some data, consumed)
  | _ -> Some (None, (0 <: consumed_length input))

let parse_option_bare_injective (#k: parser_kind) (#t: Type) (p: parser k t) (b1 b2: bytes) : Lemma
  (requires (injective_precond (parse_option_bare p) b1 b2))
  (ensures (injective_postcond (parse_option_bare p) b1 b2))
= parser_kind_prop_equiv k p;
  match parse p b1, parse p b2 with
  | Some _, Some _ -> assert (injective_precond p b1 b2)
  | _ -> ()

let parse_option (#k: parser_kind) (#t: Type) (p: parser k t) : Tot (parser (parse_option_kind k) (option t)) =
  Classical.forall_intro_2 (fun x -> Classical.move_requires (parse_option_bare_injective p x));
  parser_kind_prop_equiv k p;
  parser_kind_prop_equiv (parse_option_kind k) (parse_option_bare p);
  parse_option_bare p

let serialize_option_bare (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) : Tot (bare_serializer (option t)) =
  fun x -> match x with
  | None -> Seq.empty
  | Some y -> serialize s y

let serialize_option_bare_correct (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) : Lemma
  (requires (k.parser_kind_low > 0))
  (ensures (serializer_correct (parse_option p) (serialize_option_bare s)))
= parser_kind_prop_equiv k p

let serialize_option (#k: parser_kind) (#t: Type) (#p: parser k t) (s: serializer p) (u: squash (k.parser_kind_low > 0)) : Tot (serializer (parse_option p)) =
  serialize_option_bare_correct s;
  serialize_option_bare s
