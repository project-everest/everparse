module LowParse.Spec.Defaultable
include LowParse.Spec.Base
include LowParse.Spec.Combinators

module Seq = FStar.Seq

let parse_defaultable_bare (#k: parser_kind) (#t : Type) (defaultablev : option t) (p: parser k t) : Tot (bare_parser t) =
  fun (input : bytes) ->
    match defaultablev with
    | None -> parse p input
    | Some v -> if (Seq.length input = 0) then Some (v, 0) else (parse p input)

let parse_defaultable_bare_injective (#k : parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) (b1 b2 : bytes) : Lemma
  (requires (k.parser_kind_injective == true /\ (parse_defaultable_injective_cond_prop defaultablev p) /\ (injective_precond (parse_defaultable_bare defaultablev p) b1 b2)))
  (ensures (injective_postcond (parse_defaultable_bare defaultablev p) b1 b2))
= parser_kind_prop_equiv k p;
  match defaultablev with
  | None -> assert (injective_precond p b1 b2)
  | Some v -> match (Seq.length b1 = 0), (Seq.length b2 = 0) with
             | true, true -> ()
             | true, false -> assert (parse_defaultable_injective_cond defaultablev p b2)
             | false, true -> assert (parse_defaultable_injective_cond defaultablev p b1)
             | false, false -> assert (injective_precond p b1 b2)

let parse_defaultable (#k: parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) : Pure (parser (parse_defaultable_kind k) t) 
  (requires (parse_defaultable_injective_cond_prop defaultablev p))
  (ensures (fun _ -> True))
= Classical.forall_intro_2 (fun x -> Classical.move_requires (parse_defaultable_bare_injective defaultablev p x));  
  parser_kind_prop_equiv k p;
  parser_kind_prop_equiv (parse_defaultable_kind k) (parse_defaultable_bare defaultablev p);
  parse_defaultable_bare defaultablev p

let tot_parse_defaultable_bare (#k: parser_kind) (#t : Type) (defaultablev : option t) (p: tot_parser k t) : Tot (tot_bare_parser t) =
  fun (input : bytes) ->
    match defaultablev with
    | None -> p input
    | Some v -> if (Seq.length input = 0) then Some (v, 0) else (p input)

let tot_parse_defaultable #k #t defaultablev p =
  parser_kind_prop_ext
    (parse_defaultable_kind k) 
    (parse_defaultable #k defaultablev p)
    (tot_parse_defaultable_bare defaultablev p);
  tot_parse_defaultable_bare defaultablev p

let and_then_defaultable'
  (#k : parser_kind)
  (#t : eqtype)
  (p : parser k t)
  (#k' : parser_kind)
  (#t' : Type)
  (fp : t -> parser k' t')
  (defv : option t')
  (input : bytes)
: Lemma
  (requires (and_then_cases_injective fp /\ (forall (v : t). parse_defaultable_injective_cond_prop defv (fp v))))
  (ensures (parse_defaultable_injective_cond defv (p `and_then` fp) input))
= match defv with
  | None -> ()
  | Some dv -> 
    let _ = and_then_eq p fp input in
    match parse p input with
    | Some (id, l) -> 
	let input' = Seq.slice input l (Seq.length input) in
        assert (parse_defaultable_injective_cond defv (fp id) input')
    | None -> ()

let and_then_defaultable
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
= Classical.forall_intro (Classical.move_requires (and_then_defaultable' p fp defv))

let nondep_then_defaultable'
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t)
  (defv : option t)
  (#k' : parser_kind)
  (#t' : Type)
  (p' : parser k' t')
  (defv' : option t')
  (input : bytes)
: Lemma
  (requires (parse_defaultable_injective_cond_prop defv p))
  (ensures (parse_defaultable_injective_cond (mk_option_tuple defv defv') (p `nondep_then` p') input))
= match defv, defv' with
  | None, _ -> ()
  | _, None -> ()
  | Some dv, Some dv' -> 
    let _ = nondep_then_eq p p' input in
    match parse p input with
    | Some (v, l) ->
        assert (~ (v == dv));
	(let input' = Seq.slice input l (Seq.length input) in
        match parse p' input' with
        | Some (v', l') ->
          assert (~ ((v, v') == (dv, dv')))
        | None -> ())
    | None -> ()

let nondep_then_defaultable
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
= Classical.forall_intro (Classical.move_requires (nondep_then_defaultable' p defv p' defv'))

let nondep_then_defaultable_snd'
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t)
  (defv : option t)
  (#k' : parser_kind)
  (#t' : Type)
  (p' : parser k' t')
  (defv' : option t')
  (input : bytes)
: Lemma
  (requires (parse_defaultable_injective_cond_prop defv' p'))
  (ensures (parse_defaultable_injective_cond (mk_option_tuple defv defv') (p `nondep_then` p') input))
= match defv, defv' with
  | None, _ -> ()
  | _, None -> ()
  | Some dv, Some dv' -> 
    let _ = nondep_then_eq p p' input in
    match parse p input with
    | Some (v, l) ->
	(let input' = Seq.slice input l (Seq.length input) in
        match parse p' input' with
        | Some (v', l') ->
          assert (~ ((v, v') == (dv, dv')))
        | None -> ())
    | None -> ()

let nondep_then_defaultable_snd
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
= Classical.forall_intro (Classical.move_requires (nondep_then_defaultable_snd' p defv p' defv'))

let defaultable_trivial_eq
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t)
: Lemma
  (ensures (forall input. parse (parse_defaultable None p) input == parse p input))
= ()

let eq_defaultable
  (#k : parser_kind)
  (#t : Type)
  (p : parser k t)
  (defv : option t)
  (#k' : parser_kind)
  (p' : parser k' t)
: Lemma
  (requires (parse_defaultable_injective_cond_prop defv p) /\ (forall input. parse p input == parse p' input))
  (ensures (parse_defaultable_injective_cond_prop defv p'))
= ()
