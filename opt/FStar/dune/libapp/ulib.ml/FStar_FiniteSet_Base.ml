open Prims
type ('a, 'f, 'xs) has_elements = unit
type 'a set = ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t
let mem (x : 'a) (s : 'a set) : Prims.bool= s x
let rec list_nonrepeating : 'a . 'a Prims.list -> Prims.bool =
  fun xs ->
    match xs with
    | [] -> true
    | hd::tl ->
        (Prims.op_Negation (FStar_List_Tot_Base.mem hd tl)) &&
          (list_nonrepeating tl)
let rec remove_repeats : 'a . 'a Prims.list -> 'a Prims.list =
  fun xs ->
    match xs with
    | [] -> []
    | hd::tl ->
        let tl' = remove_repeats tl in
        if FStar_List_Tot_Base.mem hd tl then tl' else hd :: tl'
let intro_set
  (f : ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t)
  (xs : unit) : 'a set= f
let emptyset (uu___ : unit) : 'a set=
  intro_set (FStar_FunctionalExtensionality.on_domain (fun uu___1 -> false))
    ()
let insert (x : 'a) (s : 'a set) : 'a set=
  intro_set
    (FStar_FunctionalExtensionality.on_domain (fun x' -> (x = x') || (s x')))
    ()
let singleton (x : 'a) : 'a set= insert x (emptyset ())
let rec union_lists : 'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun xs ys -> match xs with | [] -> ys | hd::tl -> hd :: (union_lists tl ys)
let union (s1 : 'a set) (s2 : 'a set) : 'a set=
  intro_set
    (FStar_FunctionalExtensionality.on_domain (fun x -> (s1 x) || (s2 x))) ()
let rec intersect_lists :
  'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun xs ys ->
    match xs with
    | [] -> []
    | hd::tl ->
        let zs' = intersect_lists tl ys in
        if FStar_List_Tot_Base.mem hd ys then hd :: zs' else zs'
let intersection (s1 : 'a set) (s2 : 'a set) : 'a set=
  intro_set
    (FStar_FunctionalExtensionality.on_domain (fun x -> (s1 x) && (s2 x))) ()
let rec difference_lists :
  'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun xs ys ->
    match xs with
    | [] -> []
    | hd::tl ->
        let zs' = difference_lists tl ys in
        if FStar_List_Tot_Base.mem hd ys then zs' else hd :: zs'
let difference (s1 : 'a set) (s2 : 'a set) : 'a set=
  intro_set
    (FStar_FunctionalExtensionality.on_domain
       (fun x -> (s1 x) && (Prims.op_Negation (s2 x)))) ()
type ('a, 's1, 's2) subset = unit
type ('a, 's1, 's2) equal = unit
type ('a, 's1, 's2) disjoint = unit
let remove (x : 'a) (s : 'a set) : 'a set= difference s (singleton x)
let notin (x : 'a) (s : 'a set) : Prims.bool= Prims.op_Negation (mem x s)
type empty_set_contains_no_elements_fact = unit
type length_zero_fact = unit
type singleton_contains_argument_fact = unit
type singleton_contains_fact = unit
type singleton_cardinality_fact = unit
type insert_fact = unit
type insert_contains_argument_fact = unit
type insert_contains_fact = unit
type insert_member_cardinality_fact = unit
type insert_nonmember_cardinality_fact = unit
type union_contains_fact = unit
type union_contains_element_from_first_argument_fact = unit
type union_contains_element_from_second_argument_fact = unit
type union_of_disjoint_fact = unit
type intersection_contains_fact = unit
type union_idempotent_right_fact = unit
type union_idempotent_left_fact = unit
type intersection_idempotent_right_fact = unit
type intersection_idempotent_left_fact = unit
type intersection_cardinality_fact = unit
type difference_contains_fact = unit
type difference_doesnt_include_fact = unit
type difference_cardinality_fact = unit
type subset_fact = unit
type equal_fact = unit
type equal_extensionality_fact = unit
type disjoint_fact = unit
type insert_remove_fact = unit
type remove_insert_fact = unit
type set_as_list_cardinality_fact = unit
type all_finite_set_facts = unit
let rec remove_from_nonrepeating_list :
  'a . 'a -> 'a Prims.list -> 'a Prims.list =
  fun x xs ->
    match xs with
    | hd::tl ->
        if x = hd then tl else hd :: (remove_from_nonrepeating_list x tl)
