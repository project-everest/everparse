module LowParse.Tot.Defaultable
include LowParse.Spec.Defaultable
include LowParse.Tot.Combinators

let parse_defaultable_injective_cond (#k : parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) (b : bytes) : GTot Type0 =
  parse_defaultable_injective_cond #k defaultablev p b

let parse_defaultable_injective_cond_prop (#k : parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) : GTot Type0 =
  parse_defaultable_injective_cond_prop #k defaultablev p

val parse_defaultable (#k: parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) : Pure (parser (parse_defaultable_kind k) t) 
  (requires (parse_defaultable_injective_cond_prop defaultablev p))
  (ensures (fun y ->
    forall x . parse y x == parse (parse_defaultable #k defaultablev p) x
  ))

let parse_defaultable #k #t = tot_parse_defaultable #k #t

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

let and_then_defaultable #k #t p #k' #t' fp defv =
  and_then_defaultable #k #t p #k' #t' fp defv

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

let nondep_then_defaultable #k #t p defv #k' #t' p' defv' =
  nondep_then_defaultable #k #t p defv #k' #t' p' defv'

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

let nondep_then_defaultable_snd #k #t p defv #k' #t' p' defv' =
  nondep_then_defaultable_snd #k #t p defv #k' #t' p' defv'

val defaultable_trivial_eq
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t)
: Lemma
  (ensures (forall input. parse (parse_defaultable None p) input == parse p input))

let defaultable_trivial_eq #k #t p = defaultable_trivial_eq #k #t p

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

let eq_defaultable #k #t p defv #k' p' = eq_defaultable #k #t p defv #k' p'
