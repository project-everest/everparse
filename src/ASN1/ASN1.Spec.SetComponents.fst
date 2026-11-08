module ASN1.Spec.SetComponents

(* SET { ... }: in DER, the components of a SET are encoded in the canonical
   order of their tags (X.690 10.3, 8.6), and absent OPTIONAL components,
   as well as DEFAULT components equal to their default value, are omitted
   (X.690 11.5.)

   The contents are parsed as a list of elements, each of which is the
   encoding of one component, identified by its tag. The list must be
   strictly sorted by tag (which rules out duplicates), and each mandatory
   component must be present. The resulting value is the tuple of the
   components, in the order of their declaration (the same type as for
   SEQUENCE.) *)

open ASN1.Base

open LowParse.Tot.Base
open LowParse.Tot.Combinators
open LowParse.Tot.List

open ASN1.Spec.IdentifierU32
open ASN1.Spec.Sequence

module List = FStar.List.Tot
module Set = FStar.Set
module U32 = FStar.UInt32

(* Elements: the encoding of one component *)

let rec set_elem_t (its : list gen_decorated_parser_twin) : Tot Type (decreases its) =
  match its with
  | [] -> False
  | hd :: tl -> either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)

let rec parse_set_elem_twin
  (its : list gen_decorated_parser_twin)
  (id : asn1_id_t)
: Tot (asn1_strong_parser (set_elem_t its)) (decreases its)
= match its with
  | [] -> fail_parser _ _
  | hd :: tl ->
    let (| s, _, _ |) = Mkgendcparser?.d hd in
    if Set.mem id s
    then parse_synth (parse_asn1_sequence_item_twin hd id) (Inl #_ #(set_elem_t tl))
    else parse_synth (parse_set_elem_twin tl id) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd)))

#push-options "--z3rlimit 32 --fuel 1 --ifuel 1"
let rec parse_set_elem_twin_cases_injective
  (its : list gen_decorated_parser_twin)
: Lemma
  (ensures (and_then_cases_injective (parse_set_elem_twin its)))
  (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    let (| s, _, _ |) = Mkgendcparser?.d hd in
    parse_asn1_sequence_item_twin_cases_injective hd;
    parse_set_elem_twin_cases_injective tl;
    let p = parse_set_elem_twin its in
    and_then_cases_injective_intro p (fun id1 id2 b1 b2 ->
      parse_synth_eq (parse_asn1_sequence_item_twin hd id1) (Inl #_ #(set_elem_t tl)) b1;
      parse_synth_eq (parse_asn1_sequence_item_twin hd id2) (Inl #_ #(set_elem_t tl)) b2;
      parse_synth_eq (parse_set_elem_twin tl id1) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b1;
      parse_synth_eq (parse_set_elem_twin tl id2) (Inr #(asn1_decorated_t (Mkgendcparser?.d hd))) b2;
      if Set.mem id1 s && Set.mem id2 s
      then and_then_cases_injective_elim (parse_asn1_sequence_item_twin hd) id1 id2 b1 b2
      else if not (Set.mem id1 s) && not (Set.mem id2 s)
      then and_then_cases_injective_elim (parse_set_elem_twin tl) id1 id2 b1 b2
      else ()
    )
#pop-options

let parse_set_elem
  (its : list gen_decorated_parser_twin)
: Tot (asn1_strong_parser (set_elem_t its))
= parse_set_elem_twin_cases_injective its;
  weaken asn1_strong_parser_kind (parse_asn1_identifier_U32 `and_then` parse_set_elem_twin its)

(* The tag of the encoding of a component, if the component is encoded *)

let asn1_k_tag (#s : _) (k : asn1_k s) (v : asn1_t k) : Tot asn1_id_t =
  match k with
  | ASN1_ILC id _ -> id
  | ASN1_CHOICE_ILC lc _ ->
    let v' : make_gen_choice_type (asn1_lc_t lc) = v in
    dfst v'
  | ASN1_ANY_ILC ->
    let v' : asn1_value = v in
    (match v' with
     | ASN1_VALUE_PRIMITIVE id _ -> id
     | ASN1_VALUE_CONSTRUCTED id _ -> id)

let decorated_tag (d : asn1_gen_item_k) (v : asn1_decorated_t d) : Tot (option asn1_id_t) =
  match d with
  | (| _, _, dk |) ->
    match dk with
    | ASN1_PLAIN_ILC k -> Some (asn1_k_tag k v)
    | ASN1_OPTION_ILC k ->
      let v0 : option (asn1_t k) = v in
      (match v0 with
       | None -> None
       | Some v' -> Some (asn1_k_tag k v'))
    | ASN1_DEFAULT_TERMINAL id #k defv_l ->
      let defv = key_of_lit k defv_l in
      let v0 : default_tv defv = v in
      (match v0 with
       | Default -> None
       | Nondefault _ -> Some id)
    | ASN1_DEFAULT_RESTRICTED_TERMINAL id #k r defv_l ->
      let defv : parse_filter_refine (restriction_pred r) = key_of_lit k defv_l in
      let v0 : default_tv #(parse_filter_refine (restriction_pred r)) defv = v in
      (match v0 with
       | Default -> None
       | Nondefault _ -> Some id)

let rec elem_tag (its : list gen_decorated_parser_twin) (e : set_elem_t its) : Tot (option asn1_id_t) (decreases its) =
  match its with
  | hd :: tl ->
    let e0 : either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl) = e in
    match e0 with
    | Inl v -> decorated_tag (Mkgendcparser?.d hd) v
    | Inr e' -> elem_tag tl e'

(* Strictly sorted by tag, all elements being encoded *)

let opt_tag_lt (a b : option asn1_id_t) : Tot bool =
  match a, b with
  | Some a, Some b -> asn1_tag_lt a b
  | _ -> false

let rec tags_sorted (#t : Type) (key : t -> Tot (option asn1_id_t)) (l : list t) : Tot bool =
  match l with
  | [] -> true
  | [x] -> Some? (key x)
  | x :: y :: q -> opt_tag_lt (key x) (key y) && tags_sorted key (y :: q)

(* Components *)

let rec heads (#a #b : Type) (l : list (either a b)) : Tot (list a) =
  match l with
  | [] -> []
  | Inl x :: q -> x :: heads q
  | Inr _ :: q -> heads q

let rec tails (#a #b : Type) (l : list (either a b)) : Tot (list b) =
  match l with
  | [] -> []
  | Inl _ :: q -> tails q
  | Inr y :: q -> y :: tails q

let comp_ok (hd : gen_decorated_parser_twin) (h : list (asn1_decorated_t (Mkgendcparser?.d hd))) : Tot bool =
  match h with
  | [] -> Some? (generate_defaultable_item hd)
  | [_] -> true
  | _ -> false

let rec comps_ok (its : list gen_decorated_parser_twin) (l : list (set_elem_t its)) : Tot bool (decreases its) =
  match its with
  | [] -> true
  | hd :: tl ->
    let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) = l in
    comp_ok hd (heads l') && comps_ok tl (tails l')

let set_ok (its : list gen_decorated_parser_twin) (l : list (set_elem_t its)) : Tot bool =
  tags_sorted (elem_tag its) l && comps_ok its l

(* From the list of elements to the tuple of components *)

let comp_value (hd : gen_decorated_parser_twin) (h : list (asn1_decorated_t (Mkgendcparser?.d hd)) { comp_ok hd h }) : Tot (asn1_decorated_t (Mkgendcparser?.d hd)) =
  match h with
  | [v] -> v
  | [] -> Some?.v (generate_defaultable_item hd)

let rec set_to_tuple' (its : list gen_decorated_parser_twin) (l : list (set_elem_t its) { comps_ok its l }) : Tot (asn1_sequence_t (List.map Mkgendcparser?.d its)) (decreases its) =
  match its with
  | [] -> ()
  | [hd] ->
    let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t [])) = l in
    comp_value hd (heads l')
  | hd :: tl ->
    let l' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) = l in
    (comp_value hd (heads l'), set_to_tuple' tl (tails l'))

let set_to_tuple (its : list gen_decorated_parser_twin) (l : parse_filter_refine (set_ok its)) : Tot (asn1_sequence_t (List.map Mkgendcparser?.d its)) =
  set_to_tuple' its l

(* Injectivity *)

let asn1_tag_lt_irrefl (a : asn1_id_t) : Lemma (~ (asn1_tag_lt a a)) = ()

let asn1_tag_lt_trans (a b c : asn1_id_t) : Lemma (requires (asn1_tag_lt a b /\ asn1_tag_lt b c)) (ensures (asn1_tag_lt a c)) = ()

let rec tags_sorted_mem (#t : Type) (key : t -> Tot (option asn1_id_t)) (x : t) (l : list t) (y : t)
: Lemma
  (requires (tags_sorted key (x :: l) /\ List.memP y l))
  (ensures (opt_tag_lt (key x) (key y)))
  (decreases l)
= match l with
  | z :: q ->
    if FStar.IndefiniteDescription.strong_excluded_middle (y == z)
    then ()
    else begin
      tags_sorted_mem key z q y;
      let Some kx = key x in
      let Some kz = key z in
      let Some ky = key y in
      asn1_tag_lt_trans kx kz ky
    end

let rec tags_sorted_present (#t : Type) (key : t -> Tot (option asn1_id_t)) (l : list t) (y : t)
: Lemma
  (requires (tags_sorted key l /\ List.memP y l))
  (ensures (Some? (key y)))
  (decreases l)
= match l with
  | [_] -> ()
  | x :: z :: q ->
    if FStar.IndefiniteDescription.strong_excluded_middle (y == x)
    then ()
    else tags_sorted_present key (z :: q) y

let tags_sorted_tail (#t : Type) (key : t -> Tot (option asn1_id_t)) (x : t) (l : list t)
: Lemma
  (requires (tags_sorted key (x :: l)))
  (ensures (tags_sorted key l))
= ()

let rec tags_sorted_ext (#t : Type) (key : t -> Tot (option asn1_id_t)) (l1 l2 : list t)
: Lemma
  (requires (tags_sorted key l1 /\ tags_sorted key l2 /\ (forall x . List.memP x l1 <==> List.memP x l2)))
  (ensures (l1 == l2))
  (decreases l1)
= match l1, l2 with
  | [], [] -> ()
  | [], x :: _ -> assert (List.memP x l2)
  | x :: _, [] -> assert (List.memP x l1)
  | x1 :: q1, x2 :: q2 ->
    assert (List.memP x1 l2);
    assert (List.memP x2 l1);
    if FStar.IndefiniteDescription.strong_excluded_middle (x1 == x2)
    then begin
      let prf (y : t) : Lemma (List.memP y q1 <==> List.memP y q2) =
        if FStar.IndefiniteDescription.strong_excluded_middle (List.memP y q1)
        then begin
          tags_sorted_mem key x1 q1 y;
          asn1_tag_lt_irrefl (Some?.v (key x1));
          assert (List.memP y l2)
        end
        else if FStar.IndefiniteDescription.strong_excluded_middle (List.memP y q2)
        then begin
          tags_sorted_mem key x2 q2 y;
          asn1_tag_lt_irrefl (Some?.v (key x2));
          assert (List.memP y l1)
        end
        else ()
      in
      Classical.forall_intro prf;
      tags_sorted_tail key x1 q1;
      tags_sorted_tail key x2 q2;
      tags_sorted_ext key q1 q2
    end
    else begin
      tags_sorted_mem key x2 q2 x1;
      tags_sorted_mem key x1 q1 x2;
      let Some k1 = key x1 in
      let Some k2 = key x2 in
      asn1_tag_lt_trans k1 k2 k1;
      asn1_tag_lt_irrefl k1
    end

let rec memP_heads (#a #b : Type) (l : list (either a b)) (x : a)
: Lemma (List.memP (Inl #a #b x) l <==> List.memP x (heads l))
= match l with
  | [] -> ()
  | Inl _ :: q -> memP_heads q x
  | Inr _ :: q -> memP_heads q x

let rec memP_tails (#a #b : Type) (l : list (either a b)) (y : b)
: Lemma (List.memP (Inr #a #b y) l <==> List.memP y (tails l))
= match l with
  | [] -> ()
  | Inl _ :: q -> memP_tails q y
  | Inr _ :: q -> memP_tails q y

let memP_either (#a #b : Type) (l1 l2 : list (either a b))
: Lemma
  (requires (heads l1 == heads l2 /\ (forall y . List.memP y (tails l1) <==> List.memP y (tails l2))))
  (ensures (forall x . List.memP x l1 <==> List.memP x l2))
= let prf (x : either a b) : Lemma (List.memP x l1 <==> List.memP x l2) =
    match x with
    | Inl x' -> memP_heads l1 x'; memP_heads l2 x'
    | Inr y -> memP_tails l1 y; memP_tails l2 y
  in
  Classical.forall_intro prf

let rec elem_tag_present_tails
  (hd : gen_decorated_parser_twin) (tl : list gen_decorated_parser_twin)
  (l : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)))
: Lemma
  (requires (forall x . List.memP x l ==> Some? (elem_tag (hd :: tl) x)))
  (ensures ((forall y . List.memP y (tails l) ==> Some? (elem_tag tl y)) /\
            (forall v . List.memP v (heads l) ==> Some? (decorated_tag (Mkgendcparser?.d hd) v))))
= match l with
  | [] -> ()
  | _ :: q -> elem_tag_present_tails hd tl q

let default_tag (hd : gen_decorated_parser_twin)
: Lemma
  (requires (Some? (generate_defaultable_item hd)))
  (ensures (decorated_tag (Mkgendcparser?.d hd) (Some?.v (generate_defaultable_item hd)) == None))
= ()

#push-options "--z3rlimit 32 --fuel 2 --ifuel 2"
let comp_value_inj
  (hd : gen_decorated_parser_twin)
  (h1 : list (asn1_decorated_t (Mkgendcparser?.d hd)) { comp_ok hd h1 })
  (h2 : list (asn1_decorated_t (Mkgendcparser?.d hd)) { comp_ok hd h2 })
: Lemma
  (requires (comp_value hd h1 == comp_value hd h2 /\
    (forall v . List.memP v h1 ==> Some? (decorated_tag (Mkgendcparser?.d hd) v)) /\
    (forall v . List.memP v h2 ==> Some? (decorated_tag (Mkgendcparser?.d hd) v))))
  (ensures (h1 == h2))
= match h1, h2 with
  | [], [] -> ()
  | [v1], [v2] -> ()
  | [], [v2] -> default_tag hd
  | [v1], [] -> default_tag hd
#pop-options

#push-options "--z3rlimit 64 --fuel 2 --ifuel 2"
let rec set_to_tuple'_inj
  (its : list gen_decorated_parser_twin)
  (l1 : list (set_elem_t its) { comps_ok its l1 })
  (l2 : list (set_elem_t its) { comps_ok its l2 })
: Lemma
  (requires (set_to_tuple' its l1 == set_to_tuple' its l2 /\
    (forall x . List.memP x l1 ==> Some? (elem_tag its x)) /\
    (forall x . List.memP x l2 ==> Some? (elem_tag its x))))
  (ensures (forall x . List.memP x l1 <==> List.memP x l2))
  (decreases its)
= match its with
  | [] -> ()
  | hd :: tl ->
    let l1' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) = l1 in
    let l2' : list (either (asn1_decorated_t (Mkgendcparser?.d hd)) (set_elem_t tl)) = l2 in
    elem_tag_present_tails hd tl l1';
    elem_tag_present_tails hd tl l2';
    begin match tl with
    | [] ->
      comp_value_inj hd (heads l1') (heads l2');
      assert (tails l1' == []);
      assert (tails l2' == [])
    | _ ->
      comp_value_inj hd (heads l1') (heads l2');
      set_to_tuple'_inj tl (tails l1') (tails l2')
    end;
    memP_either l1' l2'
#pop-options

let set_to_tuple_injective (its : list gen_decorated_parser_twin)
: Lemma (synth_injective (set_to_tuple its))
= let prf (l1 l2 : parse_filter_refine (set_ok its))
  : Lemma (requires (set_to_tuple its l1 == set_to_tuple its l2)) (ensures (l1 == l2))
  = Classical.forall_intro (Classical.move_requires (tags_sorted_present (elem_tag its) l1));
    Classical.forall_intro (Classical.move_requires (tags_sorted_present (elem_tag its) l2));
    set_to_tuple'_inj its l1 l2;
    tags_sorted_ext (elem_tag its) l1 l2
  in
  Classical.forall_intro_2 (fun l1 -> Classical.move_requires (prf l1))

let make_asn1_set_parser
  (its : list gen_decorated_parser_twin)
: Tot (asn1_weak_parser (asn1_sequence_t (List.map Mkgendcparser?.d its)))
= set_to_tuple_injective its;
  weaken asn1_weak_parser_kind
    ((parse_list (parse_set_elem its) `parse_filter` set_ok its)
     `parse_synth` set_to_tuple its)
