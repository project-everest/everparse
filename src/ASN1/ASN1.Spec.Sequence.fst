module ASN1.Spec.Sequence

open ASN1.Base

include LowParse.Spec.Base
include LowParse.Spec.Combinators

open ASN1.Spec.IdentifierU32

module List = FStar.List.Tot
module Seq = FStar.Seq
module Bytes = FStar.Bytes
module Set = FStar.Set

(*
and asn1_decorated_k : Set.set asn1_id_t -> asn1_decorator -> Type =
| ASN1_PLAIN_ILC : #s : _ -> k : asn1_k s -> asn1_decorated_k s PLAIN
| ASN1_OPTION_ILC : #s : _ -> k : asn1_k s -> asn1_decorated_k s OPTION
| ASN1_DEFAULT_TERMINAL : id : asn1_id_t -> #k : asn1_terminal_k -> defaultv : asn1_terminal_t k -> asn1_decorated_k (Set.singleton id) DEFAULT

and asn1_gen_item_k : Type = s : Set.set asn1_id_t & d : asn1_decorator & asn1_decorated_k s d

| ASN1_SEQUENCE : items : list (asn1_gen_item_k) -> 
                  pf : (asn1_sequence_k_wf (List.map (fun x -> match x with |(| s, d, _ |) -> (s, d) ) items)) ->
                  asn1_content_k
                  
noeq
type gen_decorated_parser_twin =
| Mkgendcparser : (d : asn1_gen_item_k) -> (k : parser_kind) -> (p : parser k (asn1_decorated_pure_t d)) -> (fp : asn1_id_t -> parser k (asn1_decorated_pure_t d)) -> gen_decorated_parser_twin

*)

let mk_option_tuple
  (#t #t' : Type)
  (a : option t)
  (b : option t')
: option (t * t')
= match a, b with
  | None, _
  | _, None -> None
  | Some u, Some v -> Some (u, v)

let generate_defaultable_item (item : gen_decorated_parser_twin) :
  Tot (option (asn1_decorated_t (Mkgendcparser?.d item)))
= match (Mkgendcparser?.d item) with
  | (| _, _, dk |) -> match dk with
                       | ASN1_PLAIN_ILC k -> None
                       | ASN1_OPTION_ILC k -> Some (None #(asn1_t k)) 
                       | ASN1_DEFAULT_TERMINAL id #k defv -> Some (Default #(asn1_terminal_t k) #defv)

let rec generate_defaultable_items (itemtwins : list (gen_decorated_parser_twin)) :
  Tot (option (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
= match itemtwins with
  | [] -> Some ()
  | [hd] -> generate_defaultable_item hd
  | hd :: tl -> mk_option_tuple (generate_defaultable_item hd) (generate_defaultable_items tl)

let parse_defaultable_kind (k : parser_kind) : Tot parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = k.parser_kind_high;
  parser_kind_subkind = None;
}

let parse_defaultable_bare (#k: parser_kind) (#t : Type) (defaultablev : option t) (p: parser k t) : Tot (bare_parser t) =
  fun (input : bytes) ->
    match defaultablev with
    | None -> parse p input
    | Some v -> if (Seq.length input = 0) then Some (v, 0) else (parse p input)

let parse_defaultable_injective_cond (#k : parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) (b : bytes) : GTot Type0 =
  match defaultablev with
  | None -> True
  | Some v -> match (parse p b) with
    | None -> True
    | Some (v', _) -> ~ (v == v')

let parse_defaultable_injective_cond_prop (#k : parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) : GTot Type0 =
  forall (b : bytes) . parse_defaultable_injective_cond defaultablev p b

let parse_defaultable_bare_injective (#k : parser_kind) (#t : Type) (defaultablev : option t) (p : parser k t) (b1 b2 : bytes) : Lemma
  (requires ((parse_defaultable_injective_cond_prop defaultablev p) /\ (injective_precond (parse_defaultable_bare defaultablev p) b1 b2)))
  (ensures (injective_postcond (parse_defaultable_bare defaultablev p) b1 b2))
= 
  parser_kind_prop_equiv k p;
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

(* Use the weakest kind
   Sequence content always prefixed by length
*)

let asn1_sequence_parser_kind (itemtwins : list (gen_decorated_parser_twin)) : parser_kind = {
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = None;
  parser_kind_subkind = None;
}

let defaultv_filter (#a : eqtype) (defaultv : a) : a -> GTot bool =
  fun v -> not (v = defaultv)

let defaultv_synth (#a : eqtype) (defaultv : a) (v : a {~(v = defaultv)}) : default_tv defaultv =
  Nondefault v

let parse_asn1_sequence_item_twin (id : asn1_id_t) (item : gen_decorated_parser_twin) :
  Tot (parser (asn1_sequence_parser_kind []) (asn1_decorated_t (Mkgendcparser?.d item)))
= match item with
  | Mkgendcparser d k p fp ->
    match d with
    | (| _, _, dk|) ->
         match dk with
           | ASN1_PLAIN_ILC _ -> weaken (asn1_sequence_parser_kind []) (fp id)
           | ASN1_OPTION_ILC _ -> weaken (asn1_sequence_parser_kind []) 
                                 ((fp id) `parse_synth` (Some))
           | ASN1_DEFAULT_TERMINAL _ defaultv -> 
             weaken (asn1_sequence_parser_kind []) 
                    (((fp id)
                    `parse_filter`
                    (defaultv_filter defaultv))
                    `parse_synth`
                    (defaultv_synth defaultv))

let parse_asn1_sequence_item_twin_nondefault
  (id : asn1_id_t)
  (item : gen_decorated_parser_twin)
  (input : bytes)
: Lemma
  (ensures (parse_defaultable_injective_cond (generate_defaultable_item item) (parse_asn1_sequence_item_twin id item) input))
= let p = (parse_asn1_sequence_item_twin id item) in
  let t = asn1_decorated_pure_t (Mkgendcparser?.d item) in
  match item with
  | Mkgendcparser d _ _ fp ->
    match d with
    | (| _, _, dk|) ->
        match dk with
        | ASN1_PLAIN_ILC _ -> _
        | ASN1_OPTION_ILC _ -> 
          let defv = generate_defaultable_item item in
          (match parse p input with
           | None -> ()
           | Some (v, _) -> 
             let _ = parse_synth_eq (fp id) (Some) input in
             ())
        | ASN1_DEFAULT_TERMINAL _ defaultv ->
          let defv = generate_defaultable_item item in
          (match parse p input with
           | None -> ()
           | Some (v, _) -> 
             let _ = parse_synth_eq ((fp id) `parse_filter` (defaultv_filter defaultv)) (defaultv_synth defaultv) input in
             ())
 
let rec make_asn1_sequence_parser_body_twin
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (ploop : (l : list (gen_decorated_parser_twin) {l << itemtwins}) -> (parser (asn1_sequence_parser_kind l) (asn1_sequence_t (List.map (Mkgendcparser?.d) l))))
  (id : asn1_id_t)
  : Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires True)
    (ensures (fun p -> parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p))
= match itemtwins with
  | [hd] ->
    (match hd with
    | Mkgendcparser d k p fp ->
      match d with
      | (| s, de, dk |) ->
        if (Set.mem id s) then
          let _ = Classical.forall_intro (parse_asn1_sequence_item_twin_nondefault id hd) in
          let p = parse_asn1_sequence_item_twin id hd in
          p
        else
          fail_parser _ _)
  | hd :: tl -> 
    match hd with
    | Mkgendcparser d k p fp ->
      match d with
      | (| s, de, dk |) ->
        if (Set.mem id s) then
          let _ = Classical.forall_intro (parse_asn1_sequence_item_twin_nondefault id hd) in
          let p = parse_asn1_sequence_item_twin id hd in
          let p' = ploop tl in
          let _ = nondep_then_defaultable p (generate_defaultable_item hd) p' (generate_defaultable_items tl) in
          weaken (asn1_sequence_parser_kind itemtwins) (p `nondep_then` p')
        else
          match de with
          | PLAIN -> fail_parser _ _
          | _ -> 
            let defv' = generate_defaultable_item hd in
            match defv' with
            | Some defv ->
            let p = parse_ret defv in
            let p' = make_asn1_sequence_parser_body_twin tl ploop id in
            let _ = nondep_then_defaultable_snd p (generate_defaultable_item hd) p' (generate_defaultable_items tl) in
            weaken (asn1_sequence_parser_kind itemtwins) (p `nondep_then` p')

let make_asn1_sequence_parser_body_twin_spec
  (#itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
  (pbodytwin : asn1_id_t -> (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))))
= (and_then_cases_injective pbodytwin)
  /\ (forall (id : asn1_id_t). parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (pbodytwin id))

let make_asn1_sequence_parser_body
  (#itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (pbodytwin : asn1_id_t -> (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))))
  : Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires (make_asn1_sequence_parser_body_twin_spec pbodytwin))
    (ensures (fun p -> parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p))
= let ov = (generate_defaultable_items itemtwins) in
  match ov with
  | None -> weaken (asn1_sequence_parser_kind itemtwins) 
                  (parse_asn1_identifier30 `and_then` pbodytwin)
  | _ -> let _ = and_then_defaultable parse_asn1_identifier30 pbodytwin (generate_defaultable_items itemtwins) in
        let p = parse_asn1_identifier30 `and_then` pbodytwin in
        weaken (asn1_sequence_parser_kind itemtwins) p

let make_asn1_sequence_parser_body_spec
  (itemtwins : list (gen_decorated_parser_twin))
  (pbody : (l : list (gen_decorated_parser_twin) {Cons? l /\ (l << itemtwins \/ (l === itemtwins /\ 0 << 1))}) -> parser (asn1_sequence_parser_kind l) (asn1_sequence_t (List.map (Mkgendcparser?.d) l)))
= match itemtwins with
  | [] -> True
  | _ -> (parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (pbody itemtwins))

let make_asn1_sequence_parser_guard
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (pbody : (l : list (gen_decorated_parser_twin) {Cons? l /\ (l << itemtwins \/ (l === itemtwins /\ 0 << 1))}) -> parser (asn1_sequence_parser_kind l) (asn1_sequence_t (List.map (Mkgendcparser?.d) l)))
  : Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires (make_asn1_sequence_parser_body_spec itemtwins pbody))
    (ensures (fun _ -> True))
= match itemtwins with
  | [] -> weaken (asn1_sequence_parser_kind itemtwins) (parse_empty)
  | _ -> weaken (asn1_sequence_parser_kind itemtwins)
        (parse_defaultable (generate_defaultable_items itemtwins) (pbody itemtwins))

let rec make_asn1_sequence_parser'
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
: Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))) 
  (requires True)
  (ensures fun p -> (parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p))
  (decreases %[itemtwins;0])
= (assume (make_asn1_sequence_parser_body_twin_spec (make_asn1_sequence_parser_body_twin itemtwins make_asn1_sequence_parser)));
  make_asn1_sequence_parser_body (make_asn1_sequence_parser_body_twin itemtwins make_asn1_sequence_parser)

and make_asn1_sequence_parser
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
: Tot (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
  (decreases %[itemtwins;1])
= make_asn1_sequence_parser_guard itemtwins (make_asn1_sequence_parser')

//#set-options "--query_stats --z3rlimit 32"

(*
let make_parser' : l:list -> (l':list {l' << l} -> (id -> parser) {cond1}) -> parser {cond2}

let make_parser_twin' : l:list -> (l': list {l' << l} -> parser {cond2})) -> (id -> parser) {cond1}

let rec make_parser_twin : (list -> (id -> parser)) {cond1} 
  fun l -> make_parser_twin' l make_parser

and make_parser : list -> parser {cond2}
  fun l -> (make_parser' l make_parser_twin)))

let rec make_asn1_sequence_parser_twin
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (id : asn1_id_t)
  : Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires True)
    (ensures (fun p -> and_then_cases_injective p))
    (decreases %[itemtwins;0])
= match itemtwins with
  | [hd] ->
    (match hd with
    | Mkgendcparser d k p fp ->
      match d with
      | (| s, de, dk |) ->
        if (Set.mem id s) then
          parse_asn1_sequence_item_twin id fp
        else
          fail_parser _ _)
  | hd :: tl -> 
    match hd with
    | Mkgendcparser d k p fp ->
      match d with
      | (| s, de, dk |) ->
        if (Set.mem id s) then
          weaken (asn1_sequence_parser_kind itemtwins)
          ((parse_asn1_sequence_item_twin id fp)
          `nondep_then`
          (make_asn1_sequence_parser tl))
        else
          match de with
          | PLAIN -> fail_parser _ _
          | _ -> 
            weaken (asn1_sequence_parser_kind itemtwins)
            (((make_asn1_sequence_parser_twin tl id)
            `parse_synth`
            (fun suf -> (generate_defaultable_item hd), suf)))

  (* if end_of_item_list then
       error
     else if id hits the first set then
       call corresponding parser
       add decorators
     else
       check decorator of first item
       if OPTION/DEFAULT then
         generate_defaultable_items
         pass the id to myself
       else
         error *)
           
and make_asn1_sequence_parser
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  : Tot (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
        (decreases %[itemtwins;1])
= match itemtwins with
  | [] -> weaken (asn1_sequence_parser_kind itemtwins) (parse_empty)
  | _ -> weaken (asn1_sequence_parser_kind itemtwins)
      (let sp =
        (parse_asn1_identifier30
        `and_then`
//        (assume (and_then_cases_injective (make_asn1_sequence_parser_twin itemtwins));
        make_asn1_sequence_parser_twin itemtwins)) in
        (assume (parse_defaultable_injective_cond_prop (generate_defaultable_items_option itemtwins) sp));
        parse_defaultable
          (generate_defaultable_items_option itemtwins)
          sp)
(*  
      let len = Seq.length input in
      if len = 0 then
        if check_defaultable itemtwins then
          Some (generate_defaultable_items itemtwins, 0)
        else
          None
      else
        (* parse first id and pass it into parser_twin *)
        admit ()
*)
(*
and make_asn1_sequence_parser_sane
    (itemtwins : list (gen_decorated_parser_twin))
    (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
    : parse_defaultable_injective_cond_prop 
      (generate_defaultable_items_option itemtwins)
      (and_then parse_asn1_identifier30 (make_asn1_sequence_parser_twin itemtwins pf))
= admit()
*)
*)
