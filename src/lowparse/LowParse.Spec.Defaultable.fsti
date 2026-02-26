module LowParse.Spec.Defaultable
include LowParse.Spec.Base
include LowParse.Spec.Combinators

let mk_option_tuple
  (#t #t' : Type)
  (a : option t)
  (b : option t')
: option (t * t')
= match a, b with
  | None, _
  | _, None -> None
  | Some u, Some v -> Some (u, v)

let parse_defaultable_kind (k : parser_kind) : Tot parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = k.parser_kind_high;
  parser_kind_subkind = None;
  parser_kind_injective = k.parser_kind_injective;
}

let parse_defaultable_injective_cond (#k : parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) (b : bytes) : GTot Type0 =
  match defaultablev with
  | None -> True
  | Some v -> match (parse p b) with
    | None -> True
    | Some (v', _) -> ~ (v == v')

let parse_defaultable_injective_cond_prop (#k : parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) : GTot Type0 =
  forall (b : bytes) . parse_defaultable_injective_cond defaultablev p b


val parse_defaultable (#k: parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) : Pure (parser (parse_defaultable_kind k) t) 
  (requires (parse_defaultable_injective_cond_prop defaultablev p))
  (ensures (fun _ -> True))

val tot_parse_defaultable (#k: parser_kind) (#t : Type) (defaultablev : option t) (p : tot_parser k t) : Pure (tot_parser (parse_defaultable_kind k) t) 
  (requires (parse_defaultable_injective_cond_prop #k defaultablev p))
  (ensures (fun y ->
    forall x . parse y x == parse (parse_defaultable #k defaultablev p) x
  ))

val and_then_defaultable
  (#k : parser_kind)
  (#t : eqtype)
  (p : parser k t)
  (#k' : parser_kind)
  (#t' : Type)
  (fp : t -> parser k' t')
  (defv : option t')
: Lemma
  (requires (and_then_cases_injective fp /\ (forall (v : t). parse_defaultable_injective_cond_prop defv (fp v))))
  (ensures (parse_defaultable_injective_cond_prop defv (p `and_then` fp)))

val nondep_then_defaultable
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t)
  (defv : option t)
  (#k' : parser_kind)
  (#t' : Type)
  (p' : parser k' t')
  (defv' : option t')
: Lemma
  (requires (parse_defaultable_injective_cond_prop defv p))
  (ensures (parse_defaultable_injective_cond_prop (mk_option_tuple defv defv') (p `nondep_then` p')))

val nondep_then_defaultable_snd
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t)
  (defv : option t)
  (#k' : parser_kind)
  (#t' : Type)
  (p' : parser k' t')
  (defv' : option t')
: Lemma
  (requires (parse_defaultable_injective_cond_prop defv' p'))
  (ensures (parse_defaultable_injective_cond_prop (mk_option_tuple defv defv') (p `nondep_then` p')))

val defaultable_trivial_eq
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t)
: Lemma
  (ensures (forall input. parse (parse_defaultable None p) input == parse p input))

val eq_defaultable
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t)
  (defv : option t)
  (#k' : parser_kind)
  (p' : parser k' t)
: Lemma
  (requires (parse_defaultable_injective_cond_prop defv p) /\ (forall input. parse p input == parse p' input))
  (ensures (parse_defaultable_injective_cond_prop defv p'))
