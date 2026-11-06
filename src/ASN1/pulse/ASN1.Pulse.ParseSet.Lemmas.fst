module ASN1.Pulse.ParseSet.Lemmas

(* SET { ... } whose components are declared in the canonical order of their
   tags (every tag of a component is smaller than every tag of each later
   component): DER then encodes the present components in their order of
   declaration, so that the SET parser agrees with the SEQUENCE parser on the
   same items, and the zero-copy SEQUENCE parser can be reused.

   (In general, the encoding of a component of a SET may occur anywhere in
   the contents, which would require taking a subslice out of the middle of
   the input, which is not possible while keeping the rest of the input.) *)

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.List

open ASN1.Base
open ASN1.Spec.IdentifierU32
open ASN1.Spec.Sequence
open ASN1.Spec.SetComponents

module Seq = FStar.Seq
module Set = FStar.Set
module LS = LowParse.Spec.List
module C = ASN1.Spec.Conformance
module TS = ASN1.Spec.ToValue.Sound
module Sq = ASN1.Pulse.Sequence
module SC = ASN1.Pulse.SetComp
module L = ASN1.Pulse.ParseSequence.Lemmas
module P = ASN1.Pulse.Parse

(* Canonical declaration order *)

let rec items_set (its: list gen_decorated_parser_twin) : Tot (Set.set asn1_id_t) (decreases its) =
  match its with
  | [] -> Set.empty
  | hd :: tl -> Set.union (Sq.item_set hd) (items_set tl)

let rec set_canon (its: list gen_decorated_parser_twin) : Tot prop (decreases its) =
  match its with
  | [] -> True
  | hd :: tl ->
    (forall id1 id2 . (Set.mem id1 (Sq.item_set hd) /\ Set.mem id2 (items_set tl)) ==> asn1_tag_lt id1 id2) /\
    set_canon tl

let rec comp_of_id_mem (its: list gen_decorated_parser_twin) (id: asn1_id_t)
: Lemma
  (requires (Some? (SC.comp_of_id its id)))
  (ensures (Set.mem id (items_set its)))
  (decreases its)
= match its with
  | hd :: tl -> if Set.mem id (Sq.item_set hd) then () else comp_of_id_mem tl id

(* Elements of a parsed list are tagged by an identifier of their component *)

let elem_good (its: list gen_decorated_parser_twin) (e: set_elem_t its) : prop =
  match elem_tag its e with
  | None -> False
  | Some id -> SC.comp_of_id its id == Some (SC.elem_comp its e)

let all_good (its: list gen_decorated_parser_twin) (l: list (set_elem_t its)) : prop =
  forall e . List.Tot.memP e l ==> elem_good its e

#push-options "--z3rlimit 32 --fuel 2 --ifuel 1"
let rec parse_list_good (its: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (requires (C.items_tagged its))
  (ensures (match parse (parse_list (parse_set_elem its)) b with
    | Some (l, _) -> all_good its l
    | None -> True))
  (decreases (Seq.length b))
= LS.tot_parse_list_eq (parse_set_elem its) b;
  if Seq.length b = 0 then ()
  else begin
    SC.set_elem_eq its b;
    match parse (parse_set_elem its) b with
    | None -> ()
    | Some (x, n) ->
      if n = 0 then ()
      else begin
        let b' = Seq.slice b n (Seq.length b) in
        parse_list_good its b';
        match parse (parse_list (parse_set_elem its)) b' with
        | None -> ()
        | Some (q, _) ->
          assert (elem_good its x);
          assert (all_good its q);
          assert (forall e . List.Tot.memP e (x :: q) <==> (e == x \/ List.Tot.memP e q));
          assert (all_good its (x :: q))
      end
  end
#pop-options

(* Elements of a SET of two or more components *)

let as_either (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (l: list (set_elem_t (hd :: tl)))
: Tot (list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)))
= l

#push-options "--z3rlimit 64 --fuel 1 --ifuel 2"
let set_elem_cons (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (match parse (parse_set_elem (hd :: tl)) b with
    | None -> True
    | Some (e, n) ->
      begin match parse parse_asn1_identifier_U32 b with
      | None -> False
      | Some (id, n1) ->
        let e' : either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl) = e in
        match e' with
        | Inl v1 ->
          Set.mem id (Sq.item_set hd) /\
          (match parse (parse_asn1_sequence_item_twin hd id) (Seq.slice b n1 (Seq.length b)) with
            | Some (v1', n2) -> v1' == v1 /\ n1 + n2 == n
            | None -> False)
        | Inr e2 ->
          ~ (Set.mem id (Sq.item_set hd)) /\
          parse (parse_set_elem tl) b == Some (e2, n)
      end)
= parse_set_elem_twin_cases_injective (hd :: tl);
  parse_set_elem_twin_cases_injective tl;
  and_then_eq parse_asn1_identifier_U32 #asn1_strong_parser_kind #(set_elem_t (hd :: tl)) (parse_set_elem_twin (hd :: tl)) b;
  and_then_eq parse_asn1_identifier_U32 #asn1_strong_parser_kind #(set_elem_t tl) (parse_set_elem_twin tl) b;
  match parse parse_asn1_identifier_U32 b with
  | None -> ()
  | Some (id, n1) ->
    let b' = Seq.slice b n1 (Seq.length b) in
    if Set.mem id (Sq.item_set hd)
    then parse_synth_eq (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl)) b'
    else parse_synth_eq (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b'
#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec parse_list_inr (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (b: bytes)
: Lemma
  (ensures (match parse (parse_list (parse_set_elem (hd :: tl))) b with
    | Some (l, n) -> heads (as_either hd tl l) == [] ==> parse (parse_list (parse_set_elem tl)) b == Some (tails (as_either hd tl l), n)
    | None -> True))
  (decreases (Seq.length b))
= LS.tot_parse_list_eq (parse_set_elem (hd :: tl)) b;
  LS.tot_parse_list_eq (parse_set_elem tl) b;
  if Seq.length b = 0 then ()
  else begin
    set_elem_cons hd tl b;
    match parse (parse_set_elem (hd :: tl)) b with
    | None -> ()
    | Some (_, n) -> if n = 0 then () else parse_list_inr hd tl (Seq.slice b n (Seq.length b))
  end

let rec tags_sorted_tails (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (l: list (set_elem_t (hd :: tl)))
: Lemma
  (requires (heads (as_either hd tl l) == [] /\ tags_sorted (elem_tag (hd :: tl)) l))
  (ensures (tags_sorted (elem_tag tl) (tails (as_either hd tl l))))
  (decreases l)
= match l with
  | [] -> ()
  | [_] -> ()
  | x :: y :: q -> tags_sorted_tails hd tl (y :: q)
#pop-options

(* In canonical order, once an element of a later component occurs, no
   element of the first component can occur. *)

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let no_heads (hd: gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (x: set_elem_t (hd :: tl)) (q: list (set_elem_t (hd :: tl)))
: Lemma
  (requires (Inr? (x <: either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) /\
    set_canon (hd :: tl) /\ all_good (hd :: tl) (x :: q) /\ tags_sorted (elem_tag (hd :: tl)) (x :: q)))
  (ensures (heads (as_either hd tl (x :: q)) == []))
= match heads (as_either hd tl (x :: q)) with
  | [] -> ()
  | h :: _ ->
    memP_heads (as_either hd tl (x :: q)) h;
    let y : set_elem_t (hd :: tl) = Inl #_ #(set_elem_t tl) h in
    assert (List.Tot.memP y q);
    tags_sorted_mem (elem_tag (hd :: tl)) x q y;
    let Some t0 = elem_tag (hd :: tl) x in
    let Some t = elem_tag (hd :: tl) y in
    assert (SC.comp_of_id (hd :: tl) t == Some 0);
    assert (Set.mem t (Sq.item_set hd));
    assert (~ (Set.mem t0 (Sq.item_set hd)));
    comp_of_id_mem tl t0;
    asn1_tag_lt_trans t0 t t0;
    asn1_tag_lt_irrefl t0
#pop-options

(* Building a SEQUENCE parse *)

let ident_empty (b: bytes)
: Lemma (requires (Seq.length b == 0)) (ensures (parse parse_asn1_identifier_U32 b == None))
= L.identifier_nonempty b

#push-options "--fuel 2 --ifuel 2"
let compose_nil (w: bytes)
: Lemma (requires (Seq.length w == 0)) (ensures (L.seq_parsed [] w ()))
= ()
#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let compose_single_absent (hd: gen_decorated_parser_twin) (w: bytes) (v: asn1_decorated_t (Mkgendcparser?.d hd))
: Lemma (requires (Seq.length w == 0 /\ L.absent hd v)) (ensures (L.seq_parsed [hd] w v))
= TS.seq'_veq [hd] None w

let compose_single_present (hd: gen_decorated_parser_twin) (w: bytes) (v: asn1_decorated_t (Mkgendcparser?.d hd))
: Lemma (requires (L.item_parsed hd w v)) (ensures (L.seq_parsed [hd] w v))
= L.identifier_nonempty w;
  TS.seq'_veq [hd] None w;
  TS.seq''_veq [hd] None w;
  make_asn1_sequence_parser_body_twin_and_then_cases_injective [hd] make_asn1_sequence_parser';
  let pbt = make_asn1_sequence_parser_body_twin [hd] make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  and_then_eq (weaken k parse_asn1_identifier_U32) pbt w;
  match parse parse_asn1_identifier_U32 w with
  | None -> ()
  | Some (id, c1) ->
    TS.body_twin_veq_single hd id (Seq.slice w c1 (Seq.length w))
#pop-options

let cons_present_pre (hd hd': gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (w: bytes) (v1: asn1_decorated_t (Mkgendcparser?.d hd)) (v2: asn1_sequence_t (List.Tot.map Mkgendcparser?.d (hd' :: tl))) : prop =
  match parse parse_asn1_identifier_U32 w with
  | None -> False
  | Some (id, n1) ->
    Set.mem id (Sq.item_set hd) /\
    (match parse (parse_asn1_sequence_item_twin hd id) (Seq.slice w n1 (Seq.length w)) with
      | None -> False
      | Some (v1', n2) -> v1' == v1 /\ L.seq_parsed (hd' :: tl) (Seq.slice w (n1 + n2) (Seq.length w)) v2)

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let compose_cons_present (hd hd': gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (w: bytes) (v1: asn1_decorated_t (Mkgendcparser?.d hd)) (v2: asn1_sequence_t (List.Tot.map Mkgendcparser?.d (hd' :: tl)))
: Lemma
  (requires (cons_present_pre hd hd' tl w v1 v2))
  (ensures (L.seq_parsed (hd :: hd' :: tl) w (v1, v2)))
= let its = hd :: hd' :: tl in
  L.identifier_nonempty w;
  TS.seq'_veq its None w;
  TS.seq''_veq its None w;
  make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
  let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  and_then_eq (weaken k parse_asn1_identifier_U32) pbt w;
  let Some (id, c1) = parse parse_asn1_identifier_U32 w in
  let b1 = Seq.slice w c1 (Seq.length w) in
  TS.body_twin_veq_cons hd hd' tl id b1;
  let p1 = parse_asn1_sequence_item_twin hd id in
  let p2 = make_asn1_sequence_parser' (hd' :: tl) None in
  nondep_then_eq p1 p2 b1;
  let Some (_, n2) = parse p1 b1 in
  Seq.slice_slice w c1 (Seq.length w) n2 (Seq.length b1)
#pop-options

#push-options "--z3rlimit 128 --fuel 2 --ifuel 2"
let compose_cons_absent (hd hd': gen_decorated_parser_twin) (tl: list gen_decorated_parser_twin) (w: bytes) (v1: asn1_decorated_t (Mkgendcparser?.d hd)) (v2: asn1_sequence_t (List.Tot.map Mkgendcparser?.d (hd' :: tl)))
: Lemma
  (requires (L.absent hd v1 /\ L.seq_parsed (hd' :: tl) w v2 /\
    (match parse parse_asn1_identifier_U32 w with
     | None -> True
     | Some (id, _) -> ~ (Set.mem id (Sq.item_set hd)))))
  (ensures (L.seq_parsed (hd :: hd' :: tl) w (v1, v2)))
= let its = hd :: hd' :: tl in
  TS.seq'_veq its None w;
  TS.seq'_veq (hd' :: tl) None w;
  TS.seq''_veq its None w;
  TS.seq''_veq (hd' :: tl) None w;
  make_asn1_sequence_parser_body_twin_and_then_cases_injective its make_asn1_sequence_parser';
  make_asn1_sequence_parser_body_twin_and_then_cases_injective (hd' :: tl) make_asn1_sequence_parser';
  let pbt = make_asn1_sequence_parser_body_twin its make_asn1_sequence_parser' in
  let pbt' = make_asn1_sequence_parser_body_twin (hd' :: tl) make_asn1_sequence_parser' in
  let k = glb asn1_strong_parser_kind parse_ret_kind in
  and_then_eq (weaken k parse_asn1_identifier_U32) pbt w;
  and_then_eq (weaken k parse_asn1_identifier_U32) pbt' w;
  L.seq_none_some (hd' :: tl) w;
  if Seq.length w = 0
  then ident_empty w
  else match parse parse_asn1_identifier_U32 w with
  | None -> ()
  | Some (id, c1) ->
    let b1 = Seq.slice w c1 (Seq.length w) in
    TS.body_twin_veq_cons hd hd' tl id b1;
    let Mkgendcparser d _ _ = hd in
    let (| s, de, _ |) = d in
    match de with
    | PLAIN -> ()
    | _ ->
      let Some defv = generate_defaultable_item hd in
      let p1 = weaken asn1_strong_parser_kind (parse_ret defv) in
      let p2 = make_asn1_sequence_parser' (hd' :: tl) (Some id) in
      nondep_then_eq p1 p2 b1;
      Seq.lemma_eq_elim b1 (Seq.slice b1 0 (Seq.length b1))
#pop-options

(* From SET to SEQUENCE *)

let set_parsed (its: list gen_decorated_parser_twin) (w: bytes) (v: asn1_sequence_t (List.Tot.map Mkgendcparser?.d its)) : prop =
  match parse (parse_list (parse_set_elem its)) w with
  | None -> False
  | Some (l, n) -> n == Seq.length w /\ set_ok its l /\ set_to_tuple its l == v

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2"
let rec set_seq (its: list gen_decorated_parser_twin) (w: bytes) (v: asn1_sequence_t (List.Tot.map Mkgendcparser?.d its))
: Lemma
  (requires (set_canon its /\ C.items_tagged its /\ set_parsed its w v))
  (ensures (L.seq_parsed its w v))
  (decreases its)
= LS.tot_parse_list_eq (parse_set_elem its) w;
  parse_list_good its w;
  match its with
  | [] ->
    SC.set_elem_fail [] w;
    compose_nil w
  | [hd] ->
    let Some (l, _) = parse (parse_list (parse_set_elem its)) w in
    if Seq.length w = 0
    then compose_single_absent hd w v
    else begin
      set_elem_cons hd [] w;
      let Some (e, n) = parse (parse_set_elem its) w in
      let rest = Seq.slice w n (Seq.length w) in
      LS.tot_parse_list_eq (parse_set_elem its) rest;
      let l' : list (set_elem_t its) = List.Tot.tl l in
      let le : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t [])) = l' in
      (match le with
       | [] -> ()
       | Inl _ :: _ -> ()
       | Inr x :: _ -> false_elim ());
      assert (l' == []);
      assert (n == Seq.length w);
      compose_single_present hd w v
    end
  | hd :: hd' :: tl ->
    let tl' = hd' :: tl in
    let Some (l, _) = parse (parse_list (parse_set_elem its)) w in
    let v1 = fst #(asn1_decorated_t (Mkgendcparser?.d hd)) #(asn1_sequence_t (List.Tot.map Mkgendcparser?.d tl')) v in
    let v2 = snd #(asn1_decorated_t (Mkgendcparser?.d hd)) #(asn1_sequence_t (List.Tot.map Mkgendcparser?.d tl')) v in
    if Seq.length w = 0
    then begin
      LS.tot_parse_list_eq (parse_set_elem tl') w;
      assert (set_parsed tl' w v2);
      set_seq tl' w v2;
      ident_empty w;
      compose_cons_absent hd hd' tl w v1 v2
    end
    else begin
      set_elem_cons hd tl' w;
      let Some (e, n) = parse (parse_set_elem its) w in
      let l' : list (set_elem_t its) = List.Tot.tl l in
      let e' : either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl') = e in
      match e' with
      | Inl _ ->
        let rest = Seq.slice w n (Seq.length w) in
        assert (heads (as_either hd tl' l') == []);
        parse_list_inr hd tl' rest;
        tags_sorted_tails hd tl' l';
        assert (set_parsed tl' rest v2);
        set_seq tl' rest v2;
        compose_cons_present hd hd' tl w v1 v2
      | Inr _ ->
        no_heads hd tl' e l';
        parse_list_inr hd tl' w;
        tags_sorted_tails hd tl' l;
        assert (set_parsed tl' w v2);
        set_seq tl' w v2;
        compose_cons_absent hd hd' tl w v1 v2
    end
#pop-options

let set_seq_parsed (its: list gen_decorated_parser_twin) (w: bytes) (v: asn1_sequence_t (List.Tot.map Mkgendcparser?.d its))
: Lemma
  (requires (set_canon its /\ C.items_tagged its /\ P.parsed #asn1_weak_parser_kind (make_asn1_set_parser its) w v))
  (ensures (L.seq_parsed its w v))
= set_to_tuple_injective its;
  parse_synth_eq (parse_list (parse_set_elem its) `parse_filter` set_ok its) (set_to_tuple its) w;
  parse_filter_eq (parse_list (parse_set_elem its)) (set_ok its) w;
  set_seq its w v
