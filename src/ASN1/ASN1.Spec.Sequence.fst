module ASN1.Spec.Sequence

open ASN1.Base

include LowParse.Spec.Base
include LowParse.Spec.Combinators

include LowParse.Spec.Defaultable

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

let rec generate_defaultable_items (itemtwins : list (gen_decorated_parser_twin)) :
  Tot (option (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
= match itemtwins with
  | [] -> Some ()
  | [hd] -> generate_defaultable_item hd
  | hd :: tl -> mk_option_tuple (generate_defaultable_item hd) (generate_defaultable_items tl)

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
  (ploop : (l : list (gen_decorated_parser_twin)) -> (st : (option asn1_id_t) {l << itemtwins}) -> (parser (asn1_sequence_parser_kind l) (asn1_sequence_t (List.map (Mkgendcparser?.d) l))))
  (id : asn1_id_t)
  : Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires (forall l. (l << itemtwins) ==> parse_defaultable_injective_cond_prop (generate_defaultable_items l) (ploop l (Some id))))
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
    let (p, ns) =
    (match hd with
    | Mkgendcparser d k p fp ->
      match d with
      | (| s, de, dk |) ->
        if (Set.mem id s) then
          (parse_asn1_sequence_item_twin id hd, None)
        else
          match de with
          | PLAIN -> (fail_parser _ _, None)
          | _ -> 
            let defv' = generate_defaultable_item hd in
            match defv' with
            | Some defv ->
            (weaken (asn1_sequence_parser_kind []) (parse_ret defv), Some id)) in      
    let p' = ploop tl ns in
    let _ = (match hd with
    | Mkgendcparser d k pp fp ->
      match d with
      | (| s, de, dk |) ->
        if (Set.mem id s) then
          let _ = Classical.forall_intro (parse_asn1_sequence_item_twin_nondefault id hd) in
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
    weaken (asn1_sequence_parser_kind itemtwins) (p `nondep_then` p')

let make_asn1_sequence_parser_body_twin_spec
  (#itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
  (pbodytwin : asn1_id_t -> (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))))
= (and_then_cases_injective pbodytwin)
  /\ (forall (id : asn1_id_t). parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (pbodytwin id))

let make_asn1_sequence_parser_body
  (#itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
  (st : option asn1_id_t)
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (pbodytwin : asn1_id_t -> (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))))
  : Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires (make_asn1_sequence_parser_body_twin_spec pbodytwin))
    (ensures (fun p -> parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p))
= let k = glb parse_asn1_identifier30_kind parse_ret_kind in
  let p = 
  (match st with
   | None -> weaken k parse_asn1_identifier30
   | Some id -> weaken k (parse_ret id)) in
  let _ = 
  (let ov = generate_defaultable_items itemtwins in
  match ov with
  | None -> ()
  | _ -> and_then_defaultable p pbodytwin ov) in
  weaken (asn1_sequence_parser_kind itemtwins) (p `and_then` pbodytwin)

let make_asn1_sequence_parser_body_spec
  (itemtwins : list (gen_decorated_parser_twin))
  (pbody : (l : list (gen_decorated_parser_twin) {Cons? l}) -> (st : option asn1_id_t {l << itemtwins \/ (l == itemtwins /\ 0 << 1)}) -> parser (asn1_sequence_parser_kind l) (asn1_sequence_t (List.map (Mkgendcparser?.d) l)))
= match itemtwins with
  | [] -> True
  | _ -> forall id. (parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) (pbody itemtwins id))

let make_asn1_sequence_parser_guard
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (st : option asn1_id_t)
  (pbody : (l : list (gen_decorated_parser_twin) {Cons? l}) -> (st : option asn1_id_t {l << itemtwins \/ (l == itemtwins /\ 0 << 1)}) -> parser (asn1_sequence_parser_kind l) (asn1_sequence_t (List.map (Mkgendcparser?.d) l)))
  : Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
    (requires (make_asn1_sequence_parser_body_spec itemtwins pbody))
    (ensures (fun p -> match st with
                    | Some id -> parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p
                    | None -> True))
= match itemtwins with
  | [] -> (match st with
         | None -> weaken (asn1_sequence_parser_kind itemtwins) (parse_empty)
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
         weaken (asn1_sequence_parser_kind itemtwins) (parse_defaultable defv p))  

let rec make_asn1_sequence_parser''
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (st : option asn1_id_t)
: Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins))) 
  (requires True)
  (ensures fun p -> (parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p))
  (decreases %[itemtwins;0])
= (assume (make_asn1_sequence_parser_body_twin_spec (make_asn1_sequence_parser_body_twin itemtwins make_asn1_sequence_parser')));
  make_asn1_sequence_parser_body st (make_asn1_sequence_parser_body_twin itemtwins make_asn1_sequence_parser')

and make_asn1_sequence_parser'
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
  (st : option asn1_id_t)
: Pure (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
  (requires True)
  (ensures fun p -> (match st with 
                  | None -> True
                  | Some _ -> parse_defaultable_injective_cond_prop (generate_defaultable_items itemtwins) p))
  (decreases %[itemtwins;1])
= make_asn1_sequence_parser_guard itemtwins st (make_asn1_sequence_parser'')

let make_asn1_sequence_parser
  (itemtwins : list (gen_decorated_parser_twin))
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
: Tot (parser (asn1_sequence_parser_kind itemtwins) (asn1_sequence_t (List.map (Mkgendcparser?.d) itemtwins)))
= make_asn1_sequence_parser' itemtwins None

(*

(* refactor to reduce the generated code size *)

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
            weaken (asn1_sequence_parser_kind itemtwins) (p `nondep_then` p'))
            

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
*)
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
