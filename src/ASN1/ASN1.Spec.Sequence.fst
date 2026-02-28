module ASN1.Spec.Sequence

open ASN1.Base

open LowParse.Tot.Base
open LowParse.Tot.Combinators

open LowParse.Tot.Defaultable

open ASN1.Spec.IdentifierU32

module List = FStar.List.Tot
module Seq = FStar.Seq
module Bytes = FStar.Bytes
module Set = FStar.Set

let generate_defaultable_item (item : gen_decorated_parser_twin) :
  Tot (option (asn1_decorated_t (Mkgendcparser?.d item)))
= match (Mkgendcparser?.d item) with
  | (| _, _, dk |) -> match dk with
                       | ASN1_PLAIN_ILC k -> None
                       | ASN1_OPTION_ILC k -> Some (None #(asn1_t k)) 
                       | ASN1_DEFAULT_TERMINAL id #k defv -> Some (Default #(asn1_terminal_t k) #defv)
                       | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k is_valid defv -> Some (Default #(asn1_decorated_pure_t (Mkgendcparser?.d item)) #defv)

let rec generate_defaultable_items (itemtwins : list (gen_decorated_parser_twin)) :
  Tot (option (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
= match itemtwins with
  | [] -> Some ()
  | [hd] -> generate_defaultable_item hd
  | hd :: tl -> mk_option_tuple (generate_defaultable_item hd) (generate_defaultable_items tl)

let defaultv_filter (#a : eqtype) (defaultv : a) : a -> Tot bool =
  fun v -> not (v = defaultv)

let defaultv_synth (#a : eqtype) (defaultv : a) (v : a {~(v = defaultv)}) : default_tv defaultv =
  Nondefault v

let parse_asn1_sequence_item_twin (item : gen_decorated_parser_twin) :
  Tot (asn1_id_t -> asn1_strong_parser (asn1_decorated_t (Mkgendcparser?.d item)))
= match item with
  | Mkgendcparser d p fp ->
    match d with
    | (| _, _, dk|) ->
         match dk with
           | ASN1_PLAIN_ILC _ -> fun id -> (fp id)
           | ASN1_OPTION_ILC _ -> fun id -> ((fp id) `parse_synth` (Some))
           | ASN1_DEFAULT_TERMINAL _ defaultv -> fun id ->
                    (((fp id)
                    `parse_filter`
                    (defaultv_filter defaultv))
                    `parse_synth`
                    (defaultv_synth defaultv))
           | ASN1_DEFAULT_RESTRICTED_TERMINAL _ is_valid defaultv -> fun id ->
                    ((((fp id)
                    `parse_filter`
                    is_valid)
                    `parse_filter`
                    (defaultv_filter #(asn1_decorated_pure_t d) defaultv))
                    `parse_synth`
                    (defaultv_synth #(asn1_decorated_pure_t d) defaultv))


let parse_asn1_sequence_item_twin_nondefault
  (item : gen_decorated_parser_twin)
  (id : asn1_id_t)
  (input : bytes)
: Lemma
  (ensures (parse_defaultable_injective_cond (generate_defaultable_item item) (parse_asn1_sequence_item_twin item id) input))
= let p = (parse_asn1_sequence_item_twin item id) in
  match item with
  | Mkgendcparser d p' fp ->
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
        | ASN1_DEFAULT_RESTRICTED_TERMINAL _ is_valid defaultv ->
          let defv = generate_defaultable_item item in
          (match parse p input with
           | None -> ()
           | Some (v, _) -> 
             let _ = parse_synth_eq (((fp id) `parse_filter` is_valid) `parse_filter` (defaultv_filter #(asn1_decorated_pure_t d) defaultv)) (defaultv_synth  #(asn1_decorated_pure_t d) defaultv) input in
             ())


let and_then_cases_injective_some
  (#t: Type)
  (#t' : Type)
  (p': (option t -> Tot (bare_parser t')))
: GTot Type0
= forall (x1 x2: option t) (b1 b2: bytes) . {:pattern (parse (p' x1) b1); (parse (p' x2) b2)}
  and_then_cases_injective_precond p' x1 x2 b1 b2 /\ Some? x1 /\ Some? x2 ==>
  x1 == x2

let and_then_cases_injective_some_intro
  (#t:Type)
  (#t':Type)
  (p': (option t -> Tot (bare_parser t')))
  (lem: (
    (x1: option t) -> 
    (x2: option t) ->
    (b1: bytes) ->
    (b2: bytes) ->
    Lemma
    (requires (and_then_cases_injective_precond p' x1 x2 b1 b2 /\ Some? x1 /\ Some? x2))
    (ensures (x1 == x2))
  ))
: Lemma
  (and_then_cases_injective_some p')
= Classical.forall_intro_3 (fun x1 x2 b1 -> Classical.forall_intro (Classical.move_requires (lem x1 x2 b1)))

let and_then_cases_injective_elim
  (#t:Type)
  (#t':Type)
  (p': (t -> Tot (bare_parser t')))
  (x1 x2 : t)
  (b1 b2 : bytes)
  : Lemma
  (requires (and_then_cases_injective p' /\ and_then_cases_injective_precond p' x1 x2 b1 b2))
  (ensures (x1 == x2))
= () 

let and_then_cases_injective_some_elim
  (#t:Type)
  (#t':Type)
  (p': (option t -> Tot (bare_parser t')))
  (x1 x2 : t)
  (b1 b2 : bytes)
  : Lemma
  (requires (and_then_cases_injective_some p' /\ and_then_cases_injective_precond p' (Some x1) (Some x2) b1 b2))
  (ensures (x1 == x2))
= ()

#push-options "--z3rlimit 20"

let parse_asn1_sequence_item_twin_cases_injective
  (item : gen_decorated_parser_twin)
: Lemma
  (ensures (and_then_cases_injective (parse_asn1_sequence_item_twin item)))
= match item with
  | Mkgendcparser d _ fp ->
    match d with
    | (| _, _, dk|) ->
        match dk with
        | ASN1_PLAIN_ILC _ -> ()
        | ASN1_OPTION_ILC _ -> 
          let p = parse_asn1_sequence_item_twin item in
          and_then_cases_injective_intro p (
            fun id1 id2 b1 b2 ->
              parse_synth_eq (fp id1) (Some) b1;
              parse_synth_eq (fp id2) (Some) b2;
              and_then_cases_injective_elim fp id1 id2 b1 b2
          )
        | ASN1_DEFAULT_TERMINAL _ defaultv ->
          let p = parse_asn1_sequence_item_twin item in
          and_then_cases_injective_intro p (
            fun id1 id2 b1 b2 ->
              parse_synth_eq ((fp id1) `parse_filter` (defaultv_filter defaultv)) (defaultv_synth defaultv) b1;
              parse_synth_eq ((fp id2) `parse_filter` (defaultv_filter defaultv)) (defaultv_synth defaultv) b2;
              parse_filter_eq (fp id1) (defaultv_filter defaultv) b1;
              parse_filter_eq (fp id2) (defaultv_filter defaultv) b2;
              and_then_cases_injective_elim fp id1 id2 b1 b2
          )
        | ASN1_DEFAULT_RESTRICTED_TERMINAL _ is_valid defaultv ->
          let p = parse_asn1_sequence_item_twin item in
          and_then_cases_injective_intro p (
            fun id1 id2 b1 b2 ->
              parse_synth_eq (((fp id1) `parse_filter` is_valid) `parse_filter` (defaultv_filter #(asn1_decorated_pure_t d) defaultv)) (defaultv_synth #(asn1_decorated_pure_t d) defaultv) b1;
              parse_synth_eq (((fp id2) `parse_filter` is_valid) `parse_filter` (defaultv_filter #(asn1_decorated_pure_t d) defaultv)) (defaultv_synth #(asn1_decorated_pure_t d) defaultv) b2;
              parse_filter_eq ((fp id1) `parse_filter` is_valid) (defaultv_filter #(asn1_decorated_pure_t d) defaultv) b1;
              parse_filter_eq ((fp id2) `parse_filter` is_valid) (defaultv_filter #(asn1_decorated_pure_t d) defaultv) b2;
              parse_filter_eq (fp id1) is_valid b1;
              parse_filter_eq (fp id2) is_valid b2;
              and_then_cases_injective_elim fp id1 id2 b1 b2
          )
  
#pop-options

(* FIXME: using option type as the state might cause problems for extracting the validator *)

(* Thinking the loop as a fixpoint on option id so that disappears *)

(*
                  |-id-> (T)
(G) -> (B) -id-> (T) --> (G) ... -id-> (T)
 |                |
 V                V
 D
                   |-new-id--V
-Oid-> (G) -Oid-> (B) -id-> (T) -Oid-> (G) ...
        |                    |
        V                    V
        D                    S
*)

let make_asn1_sequence_parser_body_twin
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (ploop : (l : list (gen_decorated_parser_twin) {l << itemtwins}) -> (st : (option asn1_id_t)) -> (asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) l))))
  : Pure (asn1_id_t -> asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires (forall l. (l << itemtwins) ==> 
    (forall id. parse_defaultable_injective_cond_prop (generate_defaultable_items l) (ploop l (Some id)))))
    (ensures (fun fp -> 
    (forall id. parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (fp id))))
= let (ret : (id : asn1_id_t) -> (p : asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))
       {parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p})) = fun id ->
  (match itemtwins with
  | [hd] ->
    (match hd with
    | Mkgendcparser d p fp ->
      match d with
      | (| s, de, dk |) ->
        let _ = Classical.forall_intro (parse_asn1_sequence_item_twin_nondefault hd id) in
        let (p : asn1_weak_parser (asn1_sequence_t (List.map Mkgendcparser?.d itemtwins))) = weaken _ (parse_asn1_sequence_item_twin hd id) in
          //assert (parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p);
        p)
  | hd :: tl ->
    let (p, ns) =
    (match hd with
    | Mkgendcparser d p fp ->
      match d with
      | (| s, de, dk |) ->
        if (Set.mem id s) then
          (parse_asn1_sequence_item_twin hd id, None)
        else
          match de with
          | PLAIN -> (fail_parser asn1_strong_parser_kind _, None)
          | _ -> 
            let defv' = generate_defaultable_item hd in
            match defv' with
            | Some defv ->
            (weaken asn1_strong_parser_kind (parse_ret defv), Some id)) in      
    let p' = ploop tl ns in
    let _ = (match hd with
    | Mkgendcparser d pp fp ->
      match d with
      | (| s, de, dk |) ->
        if (Set.mem id s) then
          let _ = Classical.forall_intro (parse_asn1_sequence_item_twin_nondefault hd id) in
          let _ = nondep_then_defaultable p (generate_defaultable_item hd) p' (generate_defaultable_items tl) in
          ()
        else
          match de with
          | PLAIN -> ()
          | _ -> 
            let defv' = generate_defaultable_item hd in
            match defv' with
            | Some defv ->
            let _ =
              nondep_then_defaultable_snd p (generate_defaultable_item hd) p' (generate_defaultable_items tl) in
            ()) in
    let rp = weaken asn1_weak_parser_kind (p `nondep_then` p') in
    //assert (parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) rp);
    rp) in
    //assert (forall id. parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (ret id));
    ret  

#push-options "--z3rlimit 10"

let make_asn1_sequence_parser_body_twin_and_then_cases_injective
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (ploop : (l : list (gen_decorated_parser_twin) {l << itemtwins}) -> (st : (option asn1_id_t)) -> (asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) l))))
: Lemma 
    (requires (forall l. (l << itemtwins) ==> 
    (and_then_cases_injective_some (ploop l)) /\
    (forall id. parse_defaultable_injective_cond_prop (generate_defaultable_items l) (ploop l (Some id)))))
    (ensures (and_then_cases_injective (make_asn1_sequence_parser_body_twin itemtwins ploop)))
= let p = make_asn1_sequence_parser_body_twin itemtwins ploop in
    and_then_cases_injective_intro p (
      fun id1 id2 b1 b2 ->
      match itemtwins with
      | [hd] ->     
        (match hd with
        | Mkgendcparser d p fp ->
          match d with
          | (| s, de, dk |) ->
              parse_asn1_sequence_item_twin_cases_injective hd)
      | hd :: tl -> 
        (match hd with
        | Mkgendcparser d p fp ->
          match d with
          | (| s, de, dk |) ->
            match (Set.mem id1 s), (Set.mem id2 s) with
            | true, true -> 
              let p1 = parse_asn1_sequence_item_twin hd id1 in
              let p2 = parse_asn1_sequence_item_twin hd id2 in
              let p = ploop tl None in
              parse_asn1_sequence_item_twin_cases_injective hd;
              nondep_then_eq p1 p b1;
              nondep_then_eq p2 p b2
            | true, false -> 
              (match de with
              | PLAIN -> 
                let p' = fail_parser asn1_strong_parser_kind (asn1_decorated_t d) in
                let p = ploop tl None in
                nondep_then_eq p' p b2
              | _ ->  
                let p1' = parse_asn1_sequence_item_twin hd id1 in
                let p1 = ploop tl None in
                let p2' = 
                  let defv' = generate_defaultable_item hd in
                  match defv' with
                  | Some defv ->
                  (weaken asn1_strong_parser_kind (parse_ret defv)) in
                let p2 = ploop tl (Some id2) in
                nondep_then_eq p1' p1 b1;
                nondep_then_eq p2' p2 b2;
                parse_asn1_sequence_item_twin_nondefault hd id1 b1)
            | false, true ->   
              (match de with
              | PLAIN -> 
                let p' = fail_parser asn1_strong_parser_kind (asn1_decorated_t d) in
                let p = ploop tl None in
                nondep_then_eq p' p b1
              | _ ->  
                let p1' = 
                  let defv' = generate_defaultable_item hd in
                  match defv' with
                  | Some defv ->
                  (weaken asn1_strong_parser_kind (parse_ret defv)) in
                let p1 = ploop tl (Some id1) in
                let p2' = parse_asn1_sequence_item_twin hd id2 in
                let p2 = ploop tl None in
                nondep_then_eq p1' p1 b1;
                nondep_then_eq p2' p2 b2;
                parse_asn1_sequence_item_twin_nondefault hd id2 b2)          
            | false, false -> 
              match de with
              | PLAIN -> 
                let p' = fail_parser asn1_strong_parser_kind (asn1_decorated_t d) in
                let p = ploop tl None in
                nondep_then_eq p' p b1;
                nondep_then_eq p' p b2
              | _ -> 
                let p' =             
                  let defv' = generate_defaultable_item hd in
                  match defv' with
                  | Some defv ->
                    (weaken asn1_strong_parser_kind (parse_ret defv)) in
                let p1 = ploop tl (Some id1) in
                let p2 = ploop tl (Some id2) in
                nondep_then_eq p' p1 b1;
                nondep_then_eq p' p2 b2;
                and_then_cases_injective_some_elim (ploop tl) id1 id2 b1 b2))

#pop-options

let make_asn1_sequence_parser_body_twin_spec
  (#itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
  (pbodytwin : asn1_id_t -> (asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))))
= (and_then_cases_injective pbodytwin)
  /\ (forall (id : asn1_id_t). parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (pbodytwin id))

let make_asn1_sequence_parser_body
  (#itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (pbodytwin : asn1_id_t -> (asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))))
  (st : option asn1_id_t)
  : Pure (asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires (make_asn1_sequence_parser_body_twin_spec pbodytwin))
    (ensures (fun p -> parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p))
= let k = glb asn1_strong_parser_kind parse_ret_kind in
  let p =
  (match st with
   | None -> weaken k parse_asn1_identifier_U32
   | Some id -> weaken k (parse_ret id)) in
  let _ = 
  (let ov = generate_defaultable_items itemtwins in
  match ov with
  | None -> ()
  | _ -> and_then_defaultable p pbodytwin ov) in
  weaken asn1_weak_parser_kind (p `and_then` pbodytwin)

#push-options "--z3rlimit 10"

let make_asn1_sequence_parser_body_and_then_cases_injective
  (#itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (pbodytwin : asn1_id_t -> (asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))))
  : Lemma 
    (requires (make_asn1_sequence_parser_body_twin_spec pbodytwin))
    (ensures (and_then_cases_injective_some (make_asn1_sequence_parser_body pbodytwin)))
= and_then_cases_injective_some_intro (make_asn1_sequence_parser_body pbodytwin)
        (fun x1 x2 b1 b2 ->
          match x1, x2 with
          | None, _ -> _
          | _, None -> _
          | Some v1, Some v2 ->
            let k = glb asn1_strong_parser_kind parse_ret_kind in
            let p' = pbodytwin in
            let p1 = weaken k (parse_ret v1) in
            and_then_eq p1 p' b1;
            let p2 = weaken k (parse_ret v2) in
            and_then_eq p2 p' b2;
            and_then_cases_injective_elim p' v1 v2 b1 b2)

#pop-options

let make_asn1_sequence_parser_body_spec
  (itemtwins : list (gen_decorated_parser_twin))
  (pbody : (l : list (gen_decorated_parser_twin) {Cons? l /\ (l << itemtwins \/ (l == itemtwins /\ 0 << 1))}) -> (st : option asn1_id_t) -> asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) l)))
= match itemtwins with
  | [] -> True
  | _ -> and_then_cases_injective_some (pbody itemtwins) /\ (forall id. (parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (pbody itemtwins id)))

let make_asn1_sequence_parser_guard
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (pbody : (l : list (gen_decorated_parser_twin) {Cons? l /\ (l << itemtwins \/ (l == itemtwins /\ 0 << 1))}) -> (st : option asn1_id_t) -> asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) l)))
  (st : option asn1_id_t)
  : Pure (asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires (make_asn1_sequence_parser_body_spec itemtwins pbody))
    (ensures (fun p -> match st with
                    | Some id -> parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p
                    | None -> True))
= match itemtwins with
  | [] -> (match st with
         | None -> weaken asn1_weak_parser_kind (parse_empty)
         | Some _ -> fail_parser _ _)
  | _ -> (let p = 
           pbody itemtwins st in
         let defv =
           match st with
           | None -> (generate_defaultable_items itemtwins)
           | Some _ -> 
             let _ = 
               defaultable_trivial_eq p;
               eq_defaultable p (generate_defaultable_items itemtwins) (parse_defaultable None p) in
             None in
         weaken asn1_weak_parser_kind (parse_defaultable defv p))  

let make_asn1_sequence_parser_guard_and_then_cases_injective
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (pbody : (l : list (gen_decorated_parser_twin) {Cons? l /\ (l << itemtwins \/ (l == itemtwins /\ 0 << 1))}) -> (st : option asn1_id_t) -> asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) l)))
  : Lemma
  (requires (make_asn1_sequence_parser_body_spec itemtwins pbody))
  (ensures (and_then_cases_injective_some (make_asn1_sequence_parser_guard itemtwins pbody)))
= match itemtwins with
  | [] -> _
  | _ -> and_then_cases_injective_some_intro (make_asn1_sequence_parser_guard itemtwins pbody)
        (fun x1 x2 b1 b2 ->
          match x1, x2 with
          | None, _ -> _
          | _, None -> _
          | Some v1, Some v2 ->
            let fp = pbody itemtwins in
            defaultable_trivial_eq (fp x1);
            defaultable_trivial_eq (fp x2);
            and_then_cases_injective_some_elim fp v1 v2 b1 b2)

let rec make_asn1_sequence_parser''
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
: Pure (option asn1_id_t -> asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))) 
  (requires True)
  (ensures fun fp -> 
    (and_then_cases_injective_some fp) /\
    (forall st. parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (fp st)))
  (decreases %[itemtwins;0])
= let p = make_asn1_sequence_parser_body_twin itemtwins make_asn1_sequence_parser' in
  let _ = 
    (make_asn1_sequence_parser_body_twin_and_then_cases_injective itemtwins make_asn1_sequence_parser') 
  in
  assert (make_asn1_sequence_parser_body_twin_spec p);
  let _ = 
    (make_asn1_sequence_parser_body_and_then_cases_injective p) 
  in
  make_asn1_sequence_parser_body p

and make_asn1_sequence_parser'
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
: Pure (option asn1_id_t -> asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
  (requires True)
  (ensures fun fp -> 
    (and_then_cases_injective_some fp) /\
    (forall id. parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (fp (Some id))))
  (decreases %[itemtwins;1])
= assert (make_asn1_sequence_parser_body_spec itemtwins make_asn1_sequence_parser'');
  let _ = (make_asn1_sequence_parser_guard_and_then_cases_injective itemtwins make_asn1_sequence_parser'') in
  make_asn1_sequence_parser_guard itemtwins (make_asn1_sequence_parser'')

let make_asn1_sequence_parser
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
: Tot (asn1_weak_parser (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
= make_asn1_sequence_parser' itemtwins None
