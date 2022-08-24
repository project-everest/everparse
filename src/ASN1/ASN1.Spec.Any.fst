module ASN1.Spec.Any

open ASN1.Base

open LowParse.Spec.Combinators

open ASN1.Spec.Choice
open ASN1.Spec.Sequence

open ASN1.Spec.IdentifierU32

module List = FStar.List.Tot

let rec make_gen_choice_weak_payload_parser
  (#t : eqtype)
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
//  (pf : List.noRepeats (List.map fst lc))
  : Tot (id : t -> asn1_weak_parser 
                  (refine_with_tag (project_tags lc) id))
= fun id ->
  match lc with
  | [] -> fail_parser _ _
  | hd :: tl ->
    let (id', gp) = hd in
    if (id = id') then
      let p = (Mkgenparser?.p gp) in 
      parse_synth p (attach_tag lc id)
    else      
      parse_synth (make_gen_choice_weak_payload_parser tl id) (fun x -> lemma_choice_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) id x)

let make_gen_choice_weak_parser
  (#t : eqtype)
  (#k : parser_kind)
  (p : parser k t)
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
  //(pf : List.noRepeats (List.map fst lc))
  : parser (and_then_kind k asn1_weak_parser_kind) (make_gen_choice_type (extract_types lc))
= parse_tagged_union p (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc)

let make_gen_choice_weak_parser_twin
  (#t : eqtype)
  (#k : parser_kind)
  (fp : asn1_id_t -> parser k t {and_then_cases_injective fp})
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
  //(pf : List.noRepeats (List.map fst lc))
: asn1_id_t -> parser (and_then_kind k asn1_weak_parser_kind) (make_gen_choice_type (extract_types lc))
= fun id -> parse_tagged_union (fp id) (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc)

let make_gen_choice_weak_parser_twin_and_then_cases_injective
  (#t : eqtype)
  (#k : parser_kind)
  (fp : asn1_id_t -> parser k t {and_then_cases_injective fp})
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
: Lemma (ensures (and_then_cases_injective (make_gen_choice_weak_parser_twin fp lc)))
= let p = make_gen_choice_weak_parser_twin fp lc in
  and_then_cases_injective_intro p (fun x1 x2 b1 b2 ->
    parse_tagged_union_eq (fp x1) (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc) b1;
    parse_tagged_union_eq (fp x2) (tag_of_gen_choice_type (extract_types lc)) (make_gen_choice_weak_payload_parser lc) b2;
    and_then_cases_injective_elim fp x1 x2 b1 b2
  )

let tag_of_gen_choice_type_with_fallback (#key : eqtype) (lc : list (key & Type)) (fb : Type) : make_gen_choice_type_with_fallback lc fb -> Tot key = dfst

let project_tags_with_fallback (#t : eqtype) (#k : parser_kind) (lc : list (t & (gen_parser k))) (fb : gen_parser k) =
tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)

let attach_tag_with_fallback (#t : eqtype) (#k : parser_kind) (lc : list (t & (gen_parser k))) (fb : gen_parser k) (id : t) (x :  idlookup_with_fallback_t id (extract_types lc) (Mkgenparser?.t fb)) : 
  (refine_with_tag (project_tags_with_fallback lc fb) id)
= Mkdtuple2 id x

let lemma_choice_with_fallback_cast
  (#key : eqtype)
  (hd : key & Type)
  (tl : list (key & Type))
  (fb : Type)
  (id : key)
  (ret : refine_with_tag (tag_of_gen_choice_type_with_fallback tl fb) id)
: Pure (refine_with_tag (tag_of_gen_choice_type_with_fallback (hd :: tl) fb) id)
  (requires id <> (fst hd))
  (ensures (fun _ -> True))
= let (|id', v|) = ret in
  (|id', v|)

let rec make_gen_choice_with_fallback_weak_payload_parser
  (#t : eqtype)
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
  (fb : gen_parser asn1_weak_parser_kind)
//  (pf : List.noRepeats (List.map fst lc))
  : Tot (id : t -> asn1_weak_parser 
                  (refine_with_tag (project_tags_with_fallback lc fb) id))
= fun id ->
  match lc with
  | [] ->
    assert (lc == []);
    let _ = List.map_lemma (fun x -> (fst x, Mkgenparser?.t (snd x))) lc in
    assert (extract_types lc == []);
    parse_synth (Mkgenparser?.p fb) (attach_tag_with_fallback lc fb id)
  | hd :: tl ->
    let (id', gp) = hd in
    if (id = id') then
      let p = (Mkgenparser?.p gp) in 
      parse_synth p (attach_tag_with_fallback lc fb id)
    else      
      parse_synth (make_gen_choice_with_fallback_weak_payload_parser tl fb id) (fun x -> lemma_choice_with_fallback_cast (fst hd, Mkgenparser?.t (snd hd)) (extract_types tl) (Mkgenparser?.t fb) id x)

let make_gen_choice_with_fallback_weak_parser
  (#t : eqtype)
  (#k : parser_kind)
  (p : parser k t)
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
  (fb : gen_parser asn1_weak_parser_kind)
  //(pf : List.noRepeats (List.map fst lc))
  : parser (and_then_kind k asn1_weak_parser_kind) (make_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb))
= parse_tagged_union p (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb)

let make_gen_choice_with_fallback_weak_parser_twin
  (#t : eqtype)
  (#k : parser_kind)
  (fp : asn1_id_t -> parser k t {and_then_cases_injective fp})
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
  (fb : gen_parser asn1_weak_parser_kind)
  //(pf : List.noRepeats (List.map fst lc))
  : asn1_id_t -> parser (and_then_kind k asn1_weak_parser_kind) (make_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb))
= fun id -> parse_tagged_union (fp id) (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb)

let make_gen_choice_with_fallback_weak_parser_twin_and_then_cases_injective
  (#t : eqtype)
  (#k : parser_kind)
  (fp : asn1_id_t -> parser k t {and_then_cases_injective fp})
  (lc : list (t & (gen_parser asn1_weak_parser_kind)))
  (fb : gen_parser asn1_weak_parser_kind)
: Lemma (ensures (and_then_cases_injective (make_gen_choice_with_fallback_weak_parser_twin fp lc fb)))
= let p = make_gen_choice_with_fallback_weak_parser_twin fp lc fb in
  and_then_cases_injective_intro p (fun x1 x2 b1 b2 ->
    parse_tagged_union_eq (fp x1) (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb) b1;
    parse_tagged_union_eq (fp x2) (tag_of_gen_choice_type_with_fallback (extract_types lc) (Mkgenparser?.t fb)) (make_gen_choice_with_fallback_weak_payload_parser lc fb) b2;
    and_then_cases_injective_elim fp x1 x2 b1 b2
  )

let asn1_sequence_any_parser_type (l : list (gen_decorated_parser_twin)) (t : Type)
= asn1_weak_parser (asn1_sequence_any_t (List.map (Mkgendcparser?.d) l) t)

let asn1_sequence_any_parser_guard_type (itemtwins : list (gen_decorated_parser_twin)) (suffix_t : Type)
= option asn1_id_t ->
  asn1_sequence_any_parser_type itemtwins suffix_t

let asn1_sequence_any_parser_body_type  (itemtwins : list (gen_decorated_parser_twin)) (suffix_t : Type)
= asn1_id_t ->
  asn1_sequence_any_parser_type itemtwins suffix_t

let make_asn1_sequence_any_parser_body
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
  (#suffix_t : Type)
  (ploop : asn1_sequence_any_parser_guard_type (List.tl itemtwins) suffix_t)
: Pure (asn1_id_t -> asn1_sequence_any_parser_type itemtwins suffix_t)
  (requires (and_then_cases_injective_some ploop))
  (ensures (fun _ -> True))
= fun id ->
    match itemtwins with
    | hd :: tl -> match hd with 
      | Mkgendcparser d p fp ->
        let (| s, de, dk |) = d in
        let (p, ns) =
          if (Set.mem id s) then
            (parse_asn1_sequence_item_twin hd id, None)
          else
            (match de with
            | PLAIN -> (fail_parser _ _, None)
            | _ -> let defv' = generate_defaultable_item hd in
                  match defv' with
                  | Some defv -> (weaken asn1_strong_parser_kind (parse_ret defv), Some id))
        in
        weaken asn1_weak_parser_kind (p `nondep_then` (ploop ns))
    
let make_asn1_sequence_any_parser_body_and_then_cases_injective
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
  (#suffix_t : Type)
  (ploop : asn1_sequence_any_parser_guard_type (List.tl itemtwins) suffix_t)
: Lemma (requires (and_then_cases_injective_some ploop))
        (ensures (and_then_cases_injective (make_asn1_sequence_any_parser_body itemtwins ploop)))
= let p = make_asn1_sequence_any_parser_body itemtwins ploop in
  and_then_cases_injective_intro p (fun id1 id2 b1 b2 ->
    match itemtwins with | hd :: tl -> 
    match hd with | Mkgendcparser d p fp ->
    let (| s, de, dk |) = d in
    match (Set.mem id1 s), (Set.mem id2 s) with
    | true, true -> 
      let p1 = parse_asn1_sequence_item_twin hd id1 in
      let p2 = parse_asn1_sequence_item_twin hd id2 in
      let p = ploop None in
      parse_asn1_sequence_item_twin_cases_injective hd;
      nondep_then_eq p1 p b1;
      nondep_then_eq p2 p b2
    | true, false -> 
      (match de with
      | PLAIN -> 
        let p = fail_parser asn1_strong_parser_kind (asn1_decorated_t (Mkgendcparser?.d hd)) in
        nondep_then_eq p (ploop None) b2
      | _ -> match (generate_defaultable_item hd) with | Some defv ->
        let p = parse_asn1_sequence_item_twin hd id1 in
        nondep_then_eq p (ploop None) b1;
        let p' = weaken asn1_strong_parser_kind (parse_ret defv) in
        nondep_then_eq p' (ploop (Some id2)) b2;
        parse_asn1_sequence_item_twin_nondefault hd id1 b1)
    | false, true ->
      (match de with
      | PLAIN -> 
        let p = fail_parser asn1_strong_parser_kind (asn1_decorated_t (Mkgendcparser?.d hd)) in
        nondep_then_eq p (ploop None) b1
      | _ -> match (generate_defaultable_item hd) with | Some defv ->
        let p = parse_asn1_sequence_item_twin hd id2 in
        nondep_then_eq p (ploop None) b2;
        let p' = weaken asn1_strong_parser_kind (parse_ret defv) in
        nondep_then_eq p' (ploop (Some id1)) b1;
        parse_asn1_sequence_item_twin_nondefault hd id2 b2)    
    | false, false -> 
      match de with
      | PLAIN -> 
        let p = fail_parser asn1_strong_parser_kind (asn1_decorated_t (Mkgendcparser?.d hd)) in
        nondep_then_eq p (ploop None) b1
      | _ -> match (generate_defaultable_item hd) with | Some defv ->
        let p = weaken asn1_strong_parser_kind (parse_ret defv) in
        nondep_then_eq p (ploop (Some id1)) b1;
        nondep_then_eq p (ploop (Some id2)) b2;
        and_then_cases_injective_some_elim ploop id1 id2 b1 b2
  )

let make_asn1_sequence_any_parser_guard
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
  (#suffix_t : Type)
  (pbody : asn1_sequence_any_parser_body_type itemtwins suffix_t) 
  (s : option (asn1_id_t))
: Pure (asn1_sequence_any_parser_type itemtwins suffix_t)
  (requires (and_then_cases_injective pbody))
  (ensures (fun _ -> True))
= let p = 
    match s with
    | Some id -> weaken asn1_strong_parser_kind (parse_ret id)
    | None -> weaken asn1_strong_parser_kind (parse_asn1_identifier_U32)
  in
  p `and_then` pbody

let make_asn1_sequence_any_parser_guard_and_then_cases_injective
  (itemtwins : list (gen_decorated_parser_twin) {Cons? itemtwins})
  (#suffix_t : Type)
  (pbody : asn1_sequence_any_parser_body_type itemtwins suffix_t)
: Lemma 
  (requires and_then_cases_injective pbody)
  (ensures (and_then_cases_injective_some (make_asn1_sequence_any_parser_guard itemtwins pbody)))
= let p = make_asn1_sequence_any_parser_guard itemtwins pbody in
  and_then_cases_injective_some_intro p (fun s1 s2 b1 b2 ->
    match s1 with | Some x1 ->
    match s2 with | Some x2 ->
    let p1 = weaken asn1_strong_parser_kind (parse_ret x1) in
    and_then_eq p1 pbody b1;
    let p2 = weaken asn1_strong_parser_kind (parse_ret x2) in
    and_then_eq p2 pbody b2;
    and_then_cases_injective_elim pbody x1 x2 b1 b2
  )

let rec make_asn1_sequence_any_parser''
  (itemtwins : list (gen_decorated_parser_twin) {Cons?itemtwins})
  (#suffix_t : Type)
  (suffix_p_twin : parser_twin asn1_weak_parser_kind suffix_t)
: Pure (asn1_sequence_any_parser_body_type itemtwins suffix_t)
  (requires True)
  (ensures (fun fp -> and_then_cases_injective fp))
  (decreases %[itemtwins;0])
= let p = make_asn1_sequence_any_parser' (List.tl itemtwins) suffix_p_twin in
  let _ = make_asn1_sequence_any_parser_body_and_then_cases_injective itemtwins p in
  make_asn1_sequence_any_parser_body itemtwins p

and make_asn1_sequence_any_parser'
  (itemtwins : list (gen_decorated_parser_twin))
  (#suffix_t : Type)
  (suffix_p_twin : parser_twin asn1_weak_parser_kind suffix_t)
: Pure (asn1_sequence_any_parser_guard_type itemtwins suffix_t)
  (requires True)
  (ensures fun fp -> and_then_cases_injective_some fp)
  (decreases %[itemtwins;1])
= match itemtwins with
  | [] -> 
    (fun s -> match s with
    | Some id -> Mkparsertwin?.fp suffix_p_twin id
    | None -> Mkparsertwin?.p suffix_p_twin)
  | _ ->
    let p = make_asn1_sequence_any_parser'' itemtwins suffix_p_twin in
    let _ = make_asn1_sequence_any_parser_guard_and_then_cases_injective itemtwins p in
    make_asn1_sequence_any_parser_guard itemtwins p

let make_asn1_sequence_any_parser
  (itemtwins : list (gen_decorated_parser_twin))
  (#suffix_t : Type)
  (suffix_p_twin : parser_twin asn1_weak_parser_kind suffix_t)
//  (pf : (asn1_sequence_k_wf (List.map project_set_decorator itemtwins)))
: Tot (asn1_sequence_any_parser_type itemtwins suffix_t)
= make_asn1_sequence_any_parser' itemtwins suffix_p_twin None

