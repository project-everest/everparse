module CDDL.Spec

noextract
let bounded_nat (bound: nat) = (x: nat { x < bound })

let map_group_restricted_entry_list
  #b
  (g: map_group b)
  (one: bool)
: GTot (list (map_group_entry b))
= if one then g.one else g.zero_or_one

[@@erasable]
noeq
type map_group_entry_index
  #b
  (g: map_group b)
=
| Restricted:
  one: bool ->
  v: bounded_nat (List.Tot.length (map_group_restricted_entry_list g one)) ->
  map_group_entry_index g
| ZeroOrMore of bounded_nat (List.Tot.length g.zero_or_more)

noextract
let restricted_map_entry_index
  #b
  (g: map_group b)
= (x: map_group_entry_index g { Restricted? x })

let rec list_index_for_all
  (#t: Type)
  (p: t -> bool)
  (l: list t)
  (i: bounded_nat (List.Tot.length l))
: Lemma
  (requires (List.Tot.for_all p l == true))
  (ensures (p (List.Tot.index l i) == true))
  [SMTPat (List.Tot.for_all p l); SMTPat (List.Tot.index l i)]
= if i = 0
  then ()
  else list_index_for_all p (List.Tot.tl l) (i - 1)

let rec list_for_all_index
  (#t: Type)
  (p: t -> bool)
  (l: list t)
  (prf: (
    (i: bounded_nat (List.Tot.length l)) ->
    Lemma
    (ensures (p (List.Tot.index l i) == true))
  ))
: Lemma
  (List.Tot.for_all p l == true)
= match l with
  | [] -> ()
  | a :: q ->
    prf 0;
    list_for_all_index p q (fun i -> prf (i + 1))

[@@erasable]
noeq
type matches_map_group_t
  (#b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  (mg: map_group b)
= {
    f: (bounded_nat (List.Tot.length x) -> map_group_entry_index mg);
    g: (restricted_map_entry_index mg -> GTot (option (bounded_nat (List.Tot.length x))));
    prf_f: ((i: bounded_nat (List.Tot.length x)) -> Lemma
      begin match f i with
      | Restricted one j -> matches_map_group_entry (List.Tot.index (map_group_restricted_entry_list mg one) j) (List.Tot.index x i) /\ g (f i) == Some i
      | ZeroOrMore j -> matches_map_group_entry (List.Tot.index mg.zero_or_more j) (List.Tot.index x i)
      end
    );
    prf_g: ((j: restricted_map_entry_index mg) -> Lemma
      begin match g j with
      | None -> True
      | Some i -> f i == j
      end
    );
  }

noextract
let matches_map_group_prop_partial
  (#b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  (mg: map_group b)
: Tot prop
= exists (prf: matches_map_group_t x mg) . True

let matches_map_group_prop_partial_intro
  (#b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  (mg: map_group b)
  (prf: matches_map_group_t x mg)
: Lemma
  (matches_map_group_prop_partial x mg)
= ()

noextract
let matches_map_group_proof_is_final
  (#b: option Cbor.raw_data_item)
  (#x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  (#mg: map_group b)
  (prf: matches_map_group_t x mg)
: Tot prop
= (forall (j: bounded_nat (List.Tot.length mg.one)) . Some? (prf.g (Restricted true j)))

noextract
let matches_map_group_prop
  (#b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  (mg: map_group b)
: Tot prop
= exists (prf: matches_map_group_t x mg) . matches_map_group_proof_is_final prf

let matches_map_group_prop_weaken
  (#b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  (mg: map_group b)
: Lemma
  (requires (matches_map_group_prop x mg))
  (ensures (matches_map_group_prop_partial x mg))
= ()

let matches_map_group_prop_empty_intro
  (b: option Cbor.raw_data_item)
: Lemma
  (ensures (matches_map_group_prop [] (map_group_empty #b)))
= let prf : matches_map_group_t #b [] map_group_empty = {
    f = (fun x -> false_elim ());
    g = (fun x -> false_elim ());
    prf_f = (fun _ -> ());
    prf_g = (fun _ -> ());
  }
  in
  assert (exists (prf: matches_map_group_t #b [] map_group_empty) . matches_map_group_proof_is_final prf)

let matches_map_group_prop_empty_elim
  (b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (matches_map_group_prop x (map_group_empty #b)))
  (ensures (Nil? x))
= if Nil? x
  then ()
  else
    let prf = FStar.IndefiniteDescription.indefinite_description_ghost (matches_map_group_t x (map_group_empty #b)) (fun prf -> matches_map_group_proof_is_final #b #x #(map_group_empty #b) prf) in
    let _ = prf.f 0 in
    ()

let matches_map_group_prop_no_one
  (#b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  (mg: map_group b)
: Lemma
  (requires (Nil? mg.one /\ matches_map_group_prop_partial x mg))
  (ensures (matches_map_group_prop x mg))
= ()

let matches_map_group
  (#b: option Cbor.raw_data_item)
  (m: map_group b)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) {List.Tot.for_all (opt_map_entry_bounded b) x })
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (matches_map_group_prop x m)

let matches_map_group_conv
  (#b: option Cbor.raw_data_item)
  (m1: map_group b)
  (x1: list (Cbor.raw_data_item & Cbor.raw_data_item) {List.Tot.for_all (opt_map_entry_bounded b) x1 })
  (m2: map_group b)
  (x2: list (Cbor.raw_data_item & Cbor.raw_data_item) {List.Tot.for_all (opt_map_entry_bounded b) x2 })
  (f12: (
    (prf1: matches_map_group_t x1 m1) ->
    Pure (matches_map_group_t x2 m2)
    (requires (matches_map_group_proof_is_final prf1))
    (ensures (fun prf2 -> matches_map_group_proof_is_final prf2))
  ))
  (f21: (
    (prf2: matches_map_group_t x2 m2) ->
    Pure (matches_map_group_t x1 m1)
    (requires (matches_map_group_proof_is_final prf2))
    (ensures (fun prf1 -> matches_map_group_proof_is_final prf1))
  ))
: Lemma
  (matches_map_group m1 x1 == matches_map_group m2 x2)
= let phi12
    (prf1: matches_map_group_t x1 m1)
  : Lemma
    (requires (matches_map_group_proof_is_final prf1))
    (ensures (matches_map_group_prop x2 m2))
  = assert (matches_map_group_proof_is_final (f12 prf1))
  in
  let phi21
    (prf2: matches_map_group_t x2 m2)
  : Lemma
    (requires (matches_map_group_proof_is_final prf2))
    (ensures (matches_map_group_prop x1 m1))
  = assert (matches_map_group_proof_is_final (f21 prf2))
  in
  Classical.forall_intro (fun x -> Classical.move_requires phi12 x);
  Classical.forall_intro (fun x -> Classical.move_requires phi21 x)

let matches_map_group_empty
  (b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (ensures (matches_map_group (map_group_empty #b) x == Nil? x))
  [SMTPat (matches_map_group (map_group_empty #b) x)]
= Classical.move_requires (matches_map_group_prop_empty_elim b) x;
  matches_map_group_prop_empty_intro b

noextract
let rec list_find_index
  (#a:Type)
  (f:(a -> Tot bool))
  (l: list a)
: Pure (bounded_nat (List.Tot.length l))
  (requires (List.Tot.existsb f l))
  (ensures (fun i -> f (List.Tot.index l i) == true))
  (decreases l)
= let a :: q = l in
  if f a
  then 0
  else 1 + list_find_index f q

let rec list_ghost_forall_exists_find_index
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (l1: list t1)
  (l2: list t2)
  (i1: bounded_nat (List.Tot.length l1))
: Ghost (bounded_nat (List.Tot.length l2))
  (requires (list_ghost_forall_exists r l1 l2))
  (ensures (fun i2 -> r (List.Tot.index l1 i1) (List.Tot.index l2 i2)))
  (decreases l1)
= let a :: q = l1 in
  if i1 = 0
  then list_find_index (pull_rel r a) l2
  else list_ghost_forall_exists_find_index r q l2 (i1 - 1)

let rec list_exists_index_intro
  (#t: Type)
  (p: t -> bool)
  (l: list t)
  (i: bounded_nat (List.Tot.length l))
: Lemma
  (requires (p (List.Tot.index l i) == true))
  (ensures (List.Tot.existsb p l))
= if i = 0
  then ()
  else
    let a :: q = l in
    if p a
    then ()
    else list_exists_index_intro p q (i - 1)

let rec list_index_append_cons
  (#t: Type)
  (l1: list t)
  (a: t)
  (l2: list t)
: Lemma
  (ensures (
    let l' = l1 `List.Tot.append` (a :: l2) in
    let ll = List.Tot.length l1 in
    ll < List.Tot.length l' /\
    List.Tot.index l' ll == a
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | b :: q -> list_index_append_cons q a l2

let matches_map_group_no_restricted
  #b g x
= let prf1 () : Lemma
    (requires (matches_map_group g x))
    (ensures (list_ghost_forall_exists matches_map_group_entry' x g.zero_or_more))
  = let prf = FStar.IndefiniteDescription.indefinite_description_ghost (matches_map_group_t x g) (fun prf -> matches_map_group_proof_is_final prf) in
    list_for_all_index
      (list_ghost_forall_exists_body matches_map_group_entry' g.zero_or_more)
      x
      (fun i ->
        let ZeroOrMore j = prf.f i in
        prf.prf_f i;
        list_exists_index_intro (pull_rel matches_map_group_entry' (List.Tot.index x i)) g.zero_or_more j
      )
  in
  let prf2 () : Lemma
    (requires (list_ghost_forall_exists matches_map_group_entry' x g.zero_or_more
    ))
    (ensures (matches_map_group g x))
  = let prf : matches_map_group_t x g = {
      f = (fun i ->
        let j = list_ghost_forall_exists_find_index matches_map_group_entry' x g.zero_or_more i in
        ZeroOrMore j
      );
      g = (fun _ -> None);
      prf_f = (fun i -> ());
      prf_g = (fun _ -> ());
    }
    in
    assert (matches_map_group_proof_is_final prf)
  in
  Classical.move_requires prf1 ();
  Classical.move_requires prf2 ()

let rec list_ghost_forall2_refl
  (#t: Type)
  (f: t -> t -> GTot prop)
  (l: list t)
: Lemma
  (requires (forall x . f x x))
  (ensures (list_ghost_forall2 f l l))
= match l with
  | [] -> ()
  | _ :: q -> list_ghost_forall2_refl f q

let rec list_ghost_forall_exists_pointwise'
  (#t1 #t2: Type)
  (r: t1 -> t2 -> GTot prop)
  (l1: list t1)
  (l2' l2: list t2)
: Lemma
  (requires (list_ghost_forall2 r l1 l2))
  (ensures (list_ghost_forall_exists r l1 (l2' `List.Tot.append` l2)))
  (decreases l1)
= match l1, l2 with
  | [], _ -> ()
  | a1 :: q1, a2 :: q2 ->
    List.Tot.append_assoc l2' [a2] q2;
    list_index_append_cons l2' a2 q2;
    list_exists_index_intro (pull_rel r a1) (l2' `List.Tot.append` l2) (List.Tot.length l2');
    list_ghost_forall_exists_pointwise' r q1 (l2' `List.Tot.append` [a2]) q2

let list_ghost_forall_exists_pointwise
  (#t1 #t2: Type)
  (r: t1 -> t2 -> GTot prop)
  (l1: list t1)
  (l2: list t2)
: Lemma
  (requires (list_ghost_forall2 r l1 l2))
  (ensures (list_ghost_forall_exists r l1 l2))
= list_ghost_forall_exists_pointwise' r l1 [] l2

let rec list_ghost_forall2_length
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (l1: list t1)
  (l2: list t2)
: Lemma
  (requires (list_ghost_forall2 r l1 l2))
  (ensures (List.Tot.length l1 == List.Tot.length l2))
  [SMTPat (list_ghost_forall2 r l1 l2)]
= match l1, l2 with
  | _ :: q1, _ :: q2 -> list_ghost_forall2_length r q1 q2
  | _ -> ()

let rec list_ghost_forall2_index
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (l1: list t1)
  (l2: list t2)
  (i: nat)
: Lemma
  (requires (
    list_ghost_forall2 r l1 l2 /\
    (i < List.Tot.length l1 \/ i < List.Tot.length l2)
  ))
  (ensures (
    i < List.Tot.length l1 /\
    i < List.Tot.length l2 /\
    r (List.Tot.index l1 i) (List.Tot.index l2 i)
  ))
  [SMTPat (list_ghost_forall2 r l1 l2); SMTPat (List.Tot.index l1 i)]
= if i = 0
  then ()
  else list_ghost_forall2_index r (List.Tot.tl l1) (List.Tot.tl l2) (i - 1)

let list_ghost_forall_exists_is_sub_map_group_entry_of_refl
  #b
  (l: list (map_group_entry b))
: Lemma
  (ensures (list_ghost_forall_exists is_sub_map_group_entry_of l l))
  [SMTPat (list_ghost_forall_exists is_sub_map_group_entry_of l l)]
= list_ghost_forall2_refl is_sub_map_group_entry_of l;
  list_ghost_forall_exists_pointwise is_sub_map_group_entry_of l l

let map_group_included_zero_or_more_prf
  #b
  (small large: map_group b)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  (prf: matches_map_group_t x small)
: Pure (matches_map_group_t x large)
    (requires (map_group_included_zero_or_more small large))
    (ensures (fun _ -> True))
= {
    f = (fun i -> match prf.f i with
      | Restricted one j -> ZeroOrMore (list_ghost_forall_exists_find_index is_sub_map_group_entry_of (map_group_restricted_entry_list small one) large.zero_or_more j)
      | ZeroOrMore j -> ZeroOrMore (list_ghost_forall_exists_find_index is_sub_map_group_entry_of small.zero_or_more large.zero_or_more j)
    );
    g = (fun _ -> None);
    prf_f = (fun i -> prf.prf_f i);
    prf_g = (fun _ -> ())
  }

let map_group_included_zero_or_more_correct
  #b
  (small large: map_group b)
: Lemma
  (requires (map_group_included_zero_or_more small large))
  (ensures (is_sub_map_group_of small large))
= let phi
    (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  : Lemma
    (requires (
      matches_map_group_prop x small
    ))
    (ensures (
      matches_map_group_prop x large
    ))
    [SMTPat (matches_map_group_prop x small); SMTPat (matches_map_group_prop x large)]
  = let prf = FStar.IndefiniteDescription.indefinite_description_ghost (matches_map_group_t x small) (fun _ -> True) in
    matches_map_group_prop_partial_intro x large (map_group_included_zero_or_more_prf small large x prf)
  in
  ()

let map_group_ignore_restricted_entries_sub
  #b
  (mg: map_group b)
: Lemma
  (requires (
    list_ghost_forall_exists is_sub_map_group_entry_of mg.one mg.zero_or_more /\
    list_ghost_forall_exists is_sub_map_group_entry_of mg.zero_or_one mg.zero_or_more
  ))
  (ensures (
    mg `is_sub_map_group_of` map_group_ignore_restricted_entries mg
  ))
= map_group_included_zero_or_more_correct mg (map_group_ignore_restricted_entries mg)

let map_group_included_pointwise_prf
  #b
  (small large: map_group b)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  (prf: matches_map_group_t x small)
: Pure (matches_map_group_t x large)
    (requires (map_group_included_pointwise small large))
    (ensures (fun _ -> True))
= {
    f = (fun i -> match prf.f i with
      | Restricted one j -> Restricted one (j <: bounded_nat (List.Tot.length (map_group_restricted_entry_list large one)))
      | ZeroOrMore j -> ZeroOrMore (j <: bounded_nat (List.Tot.length large.zero_or_more))
    );
    g = (fun x ->
    let y = match x with
      | Restricted one j -> prf.g (Restricted one (j <: bounded_nat (List.Tot.length (map_group_restricted_entry_list small one))))
      | ZeroOrMore j -> prf.g (ZeroOrMore (j <: bounded_nat (List.Tot.length small.zero_or_more)))
    in
    match y with
    | None -> None
    | Some i -> Some i
    );
    prf_f = (fun i -> prf.prf_f i);
    prf_g = (fun i -> prf.prf_g
      begin let Restricted one j = i in
        Restricted one (j <: bounded_nat (List.Tot.length (map_group_restricted_entry_list small one)))
      end
    );
  }

let map_group_included_pointwise_correct
  #b
  (small large: map_group b)
: Lemma
  (requires (map_group_included_pointwise small large))
  (ensures (is_sub_map_group_of small large))
= let phi
    (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
  : Lemma
    (requires (
      matches_map_group_prop x small
    ))
    (ensures (
      matches_map_group_prop x large
    ))
    [SMTPat (matches_map_group_prop x small); SMTPat (matches_map_group_prop x large)]
  = let prf = FStar.IndefiniteDescription.indefinite_description_ghost (matches_map_group_t x small) (fun prf -> matches_map_group_proof_is_final prf) in
    assert (matches_map_group_proof_is_final (map_group_included_pointwise_prf small large x prf))
  in
  ()

let rec list_index_map
  (#t1 #t2: Type)
  (f: t1 -> t2)
  (l: list t1)
  (i: bounded_nat (List.Tot.length l))
: Lemma
  (List.Tot.index (List.Tot.map f l) i == f (List.Tot.index l i))
  [SMTPat (List.Tot.index (List.Tot.map f l) i)]
= if i = 0
  then ()
  else list_index_map f (List.Tot.tl l) (i - 1)

#push-options "--z3rlimit 32"

let matches_map_group_map_group_cons_zero_or_one_none_intro
   #b (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
   (prf: matches_map_group_t x g)
: Pure (matches_map_group_t x (map_group_cons_zero_or_one (map_group_entry_for k ty) true g))
    (requires (None? (Cbor.list_ghost_assoc k x)))
    (ensures (fun _ -> True))
= list_assoc_none_for_all_map_key_neq k x;
  let g' = map_group_cons_zero_or_one (map_group_entry_for k ty) true g in
  {
    f = (fun (i: bounded_nat (List.Tot.length x)) -> match prf.f i with
      | Restricted true j -> Restricted true (j <: bounded_nat (List.Tot.length g'.one))
      | Restricted false j -> Restricted false (j + 1 <: bounded_nat (List.Tot.length g'.zero_or_one))
      | ZeroOrMore j -> ZeroOrMore (j <: bounded_nat (List.Tot.length g'.zero_or_more))
    );
    g = (fun (j: restricted_map_entry_index g') ->
      match j with
      | Restricted true j -> prf.g (Restricted true (j <: bounded_nat (List.Tot.length g.one)))
      | Restricted false j -> if j = 0 then None else prf.g (Restricted false (j - 1 <: bounded_nat (List.Tot.length g.zero_or_one)))
    );
    prf_f = (fun (i: bounded_nat (List.Tot.length x)) ->
      prf.prf_f i
    );
    prf_g = (fun (j: restricted_map_entry_index g') ->
      match j with
      | Restricted true j -> prf.prf_g (Restricted true (j <: bounded_nat (List.Tot.length g.one)))
      | Restricted false j -> if j = 0 then () else prf.prf_g (Restricted false (j - 1 <: bounded_nat (List.Tot.length g.zero_or_one)))
    );
  }

let matches_map_group_map_group_cons_zero_or_one_none_elim
   #b (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
   (prf: matches_map_group_t x (map_group_cons_zero_or_one (map_group_entry_for k ty) true g))
: Pure (matches_map_group_t x g)
    (requires (None? (Cbor.list_ghost_assoc k x)))
    (ensures (fun _ -> True))
= list_assoc_none_for_all_map_key_neq k x;
  let g' = map_group_cons_zero_or_one (map_group_entry_for k ty) true g in
  {
    f = (fun (i: bounded_nat (List.Tot.length x)) -> match prf.f i with
      | Restricted true j -> Restricted true (j <: bounded_nat (List.Tot.length g.one))
      | Restricted false j ->
        prf.prf_f i; assert (j <> 0);
        Restricted false (j - 1 <: bounded_nat (List.Tot.length g.zero_or_one))
      | ZeroOrMore j -> ZeroOrMore (j <: bounded_nat (List.Tot.length g.zero_or_more))
    );
    g = (fun (j: restricted_map_entry_index g) ->
      match j with
      | Restricted true j -> prf.g (Restricted true (j <: bounded_nat (List.Tot.length g'.one)))
      | Restricted false j -> prf.g (Restricted false (j + 1 <: bounded_nat (List.Tot.length g'.zero_or_one)))
    );
    prf_f = (fun (i: bounded_nat (List.Tot.length x)) ->
      prf.prf_f i
    );
    prf_g = (fun (j: restricted_map_entry_index g) ->
      match j with
      | Restricted true j -> prf.prf_g (Restricted true (j <: bounded_nat (List.Tot.length g'.one)))
      | Restricted false j -> prf.prf_g (Restricted false (j + 1 <: bounded_nat (List.Tot.length g'.zero_or_one)))
    );
  }

#pop-options

let rec list_ghost_assoc_index
  (#t1 #t2: Type)
  (k: t1)
  (l: list (t1 & t2))
: Ghost (bounded_nat (List.Tot.length l))
  (requires (Some? (Cbor.list_ghost_assoc k l)))
  (ensures (fun i ->
    match Cbor.list_ghost_assoc k l with
    | Some v -> List.Tot.index l i == (k, v)
    | _ -> False
  ))
= let (k', _) :: l' = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
  then 0
  else 1 + list_ghost_assoc_index k l'

let rec list_filter_map_key_neq_not_memP
  (#t1 #t2: Type)
  (k: t1)
  (l: list (t1 & t2))
: Lemma
  (requires (
    (~ (List.Tot.memP k (List.Tot.map fst l)))
  ))
  (ensures (
    List.Tot.filter (map_key_neq _ k) l == l
  ))
= match l with
  | [] -> ()
  | _ :: q -> list_filter_map_key_neq_not_memP k q

let rec list_length_filter_map_key_neq_no_repeats
  (#t1 #t2: Type)
  (k: t1)
  (l: list (t1 & t2))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l)
  ))
  (ensures (
    List.Tot.length l == (if Some? (Cbor.list_ghost_assoc k l) then 1 else 0) + List.Tot.length (List.Tot.filter (map_key_neq _ k) l)
  ))
  [SMTPat [List.Tot.length (List.Tot.filter (map_key_neq _ k) l)]]
= match l with
  | [] -> ()
  | (k', _) :: l' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then list_filter_map_key_neq_not_memP k l'
    else list_length_filter_map_key_neq_no_repeats k l'

let rec list_ghost_assoc_index_no_repeats
  (#t1 #t2: Type)
  (k: t1)
  (l: list (t1 & t2))
  (i: bounded_nat (List.Tot.length l))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l) /\
    Some? (Cbor.list_ghost_assoc k l)
  ))
  (ensures (
    Some? (Cbor.list_ghost_assoc k l) /\ (
    let i0 = list_ghost_assoc_index k l in
    let Some v = Cbor.list_ghost_assoc k l in
    let l' = List.Tot.filter (map_key_neq _ k) l in
    List.Tot.length l == 1 + List.Tot.length l' /\
    List.Tot.index l i == (if i = i0 then (k, v) else List.Tot.index l' (if i < i0 then i else i - 1))
  )))
= list_length_filter_map_key_neq_no_repeats k l;
  let (k', v') :: l' = l in
  if i = 0
  then ()
  else if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
  then list_filter_map_key_neq_not_memP k l'
  else list_ghost_assoc_index_no_repeats k l' (i - 1)

let list_ghost_assoc_index_no_repeats_recip
  (#t1 #t2: Type)
  (k: t1)
  (l: list (t1 & t2))
  (i: bounded_nat (List.Tot.length (List.Tot.filter (map_key_neq _ k) l)))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l) /\
    Some? (Cbor.list_ghost_assoc k l)
  ))
  (ensures (
    Some? (Cbor.list_ghost_assoc k l) /\ (
    let i0 = list_ghost_assoc_index k l in
    let l' = List.Tot.filter (map_key_neq _ k) l in
    List.Tot.length l == 1 + List.Tot.length l' /\
    List.Tot.index l' i == List.Tot.index l (if i < i0 then i else i + 1)
  )))
= list_length_filter_map_key_neq_no_repeats k l;
  let i0 = list_ghost_assoc_index k l in
  list_ghost_assoc_index_no_repeats k l (if i < i0 then i else i + 1)

let map_group_cons_restricted #b (ge: map_group_entry b) (one: bool) (g: map_group b) : map_group b =
  if one
  then map_group_cons_one ge true g
  else map_group_cons_zero_or_one ge true g

let map_group_restricted_entry_list_map_group_cons_restricted #b (ge: map_group_entry b) (one: bool) (g: map_group b) (one': bool) : Lemma
  (map_group_restricted_entry_list (map_group_cons_restricted #b ge one g) one' == (
    if one' = one
    then ge :: List.Tot.map (cut_map_group_entry ge.fst) (map_group_restricted_entry_list g one')
    else List.Tot.map (cut_map_group_entry ge.fst) (map_group_restricted_entry_list g one')
  ))
//  [SMTPat (map_group_restricted_entry_list (map_group_cons_restricted #b ge one g) one')]
= ()

#push-options "--z3rlimit 32"
#restart-solver

let matches_map_group_map_group_cons_restricted_some_ty
   #b (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (one: bool) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (Some? (Cbor.list_ghost_assoc k x) /\ matches_map_group (map_group_cons_restricted (map_group_entry_for k ty) one g) x))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> False
    | Some y -> opt_precedes y b /\ ty y
    end
  ))
= list_ghost_assoc_for_all (opt_map_entry_bounded b) k x;
  let g' = map_group_cons_restricted (map_group_entry_for k ty) one g in
  let prf = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun (prf: matches_map_group_t x g') -> matches_map_group_proof_is_final prf) in
  let i = list_ghost_assoc_index k x in
  prf.prf_f i;
  ()

let matches_map_group_map_group_cons_restricted_some_no_repeats_intro
   #b (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (one: bool) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
   (prf: matches_map_group_t (List.Tot.filter (map_key_neq _ k) x) g)
: Pure (matches_map_group_t x (map_group_cons_restricted (map_group_entry_for k ty) one g))
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst x) /\
    begin match Cbor.list_ghost_assoc k x with
    | None -> False
    | Some y -> opt_precedes y b ==> ty y
    end
  ))
  (ensures (fun _ -> True))
= list_ghost_assoc_for_all (opt_map_entry_bounded b) k x;
  let g' = map_group_cons_restricted (map_group_entry_for k ty) one g in
  list_length_filter_map_key_neq_no_repeats k x;
  let i0 = list_ghost_assoc_index k x in
  {
    f = (fun i ->
      list_ghost_assoc_index_no_repeats k x i;
      if i = i0
      then Restricted one 0
      else begin
        let i' : bounded_nat (List.Tot.length (List.Tot.filter (map_key_neq _ k) x)) =
          if i < i0 then i else i - 1
        in
        prf.prf_f i';
        match prf.f i' with
        | Restricted one' j -> Restricted one' ((if one = one' then j + 1 else j) <: bounded_nat (List.Tot.length (map_group_restricted_entry_list g' one')))
        | ZeroOrMore j -> ZeroOrMore (j <: bounded_nat (List.Tot.length g'.zero_or_more))
      end
    );
    g = (fun j' ->
      if match j' with
      | Restricted one' j' -> one = one' && j' = 0
      then Some i0
      else
        let j = match j' with
        | Restricted one' j' -> Restricted one' ((if one = one' then j' - 1 else j') <: bounded_nat (List.Tot.length (map_group_restricted_entry_list g one')))
        in
        match prf.g j with
        | None -> None
        | Some i' ->
          list_ghost_assoc_index_no_repeats_recip k x i';
          let i : bounded_nat (List.Tot.length x) = if i' < i0 then i' else i' + 1 in
          Some i
    );
    prf_f = (fun i ->
      list_ghost_assoc_index_no_repeats k x i;
      if i = i0
      then ()
      else begin
        let i' : bounded_nat (List.Tot.length (List.Tot.filter (map_key_neq _ k) x)) =
          if i < i0 then i else i - 1
        in
        prf.prf_f i';
        ()
      end
    );
    prf_g = (fun j' ->
      if match j' with
      | Restricted one' j' -> one = one' && j' = 0
      then ()
      else
        let j = match j' with
        | Restricted one' j' -> Restricted one' ((if one = one' then j' - 1 else j') <: bounded_nat (List.Tot.length (map_group_restricted_entry_list g one')))
        in
        prf.prf_g j
    );
  }

#pop-options

#push-options "--z3rlimit 128"
#restart-solver

let matches_map_group_map_group_cons_restricted_some_no_repeats_elim
   #b (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (one: bool) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
   (prf: matches_map_group_t x (map_group_cons_restricted (map_group_entry_for k ty) one g))
: Pure (matches_map_group_t (List.Tot.filter (map_key_neq _ k) x) g)
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst x) /\
    begin match Cbor.list_ghost_assoc k x with
    | None -> False
    | Some y -> opt_precedes y b ==> ty y
    end
  ))
  (ensures (fun prf' ->
    matches_map_group_proof_is_final prf ==> matches_map_group_proof_is_final prf'
  ))
= list_ghost_assoc_for_all (opt_map_entry_bounded b) k x;
  let g' = map_group_cons_restricted (map_group_entry_for k ty) one g in
  list_length_filter_map_key_neq_no_repeats k x;
  let i0 = list_ghost_assoc_index k x in
  {
    f = (fun i' ->
      list_ghost_assoc_index_no_repeats_recip k x i';
      let i : bounded_nat (List.Tot.length x) =
        if i' < i0 then i' else i' + 1
      in
      prf.prf_f i;
      match prf.f i with
      | Restricted one' j -> Restricted one' ((if one = one' then j - 1 else j) <: bounded_nat (List.Tot.length (map_group_restricted_entry_list g one')))
      | ZeroOrMore j -> ZeroOrMore (j <: bounded_nat (List.Tot.length g.zero_or_more))
    );
    g = (fun j ->
      let j' = match j with
      | Restricted one' j -> Restricted one' ((if one = one' then j + 1 else j) <: bounded_nat (List.Tot.length (map_group_restricted_entry_list g' one')))
      in
      match prf.g j' with
      | None -> None
      | Some i ->
        list_ghost_assoc_index_no_repeats k x i;
        if i = i0 && not (Restricted?.one j)
        then None
        else begin
          prf.prf_g j';
          prf.prf_f i;
          assert (Restricted?.one j ==> i <> i0);
          let i' : bounded_nat (List.Tot.length (List.Tot.filter (map_key_neq _ k) x)) = 
            if i < i0 then i else i - 1
          in
          Some i'
        end
      );
    prf_f = (fun i' ->
      list_ghost_assoc_index_no_repeats_recip k x i';
      let i : bounded_nat (List.Tot.length x) =
        if i' < i0 then i' else i' + 1
      in
      prf.prf_f i
    );
    prf_g = (fun j ->
      let j' = match j with
      | Restricted one' j -> Restricted one' ((if one = one' then j + 1 else j) <: bounded_nat (List.Tot.length (map_group_restricted_entry_list g' one')))
      in
      prf.prf_g j';
      match prf.g j' with
      | None -> ()
      | Some i -> prf.prf_f i
    );
  }

#pop-options

let matches_map_group_map_group_cons_zero_or_one_no_repeats
   #b (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst x)))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b
    end /\
    matches_map_group (map_group_cons_zero_or_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> matches_map_group g x
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))
= list_ghost_assoc_for_all (opt_map_entry_bounded b) k x;
  match Cbor.list_ghost_assoc k x with
  | None ->
    matches_map_group_conv g x (map_group_cons_zero_or_one (map_group_entry_for k ty) true g) x
      (fun prf -> matches_map_group_map_group_cons_zero_or_one_none_intro k ty g x prf)
      (fun prf -> matches_map_group_map_group_cons_zero_or_one_none_elim k ty g x prf)
  | Some y ->
    Classical.move_requires (matches_map_group_map_group_cons_restricted_some_ty k ty false g) x;
    if ty y
    then
      let x' = List.Tot.filter (map_key_neq _ k) x in
      matches_map_group_conv g x' (map_group_cons_zero_or_one (map_group_entry_for k ty) true g) x
        (fun prf -> matches_map_group_map_group_cons_restricted_some_no_repeats_intro k ty false g x prf)
        (fun prf -> matches_map_group_map_group_cons_restricted_some_no_repeats_elim k ty false g x prf)
    else ()

let matches_map_group_map_group_cons_one_none
   #b (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (None? (Cbor.list_ghost_assoc k x)))
  (ensures (matches_map_group (map_group_cons_one (map_group_entry_for k ty) true g) x == false))
= let g' = map_group_cons_one (map_group_entry_for k ty) true g in
  if matches_map_group g' x 
  then begin
    list_assoc_none_for_all_map_key_neq k x;
    let prf = FStar.IndefiniteDescription.indefinite_description_ghost (matches_map_group_t x g') (fun (prf: matches_map_group_t x g') -> matches_map_group_proof_is_final prf) in
    let Some i = prf.g (Restricted true 0) in
    prf.prf_g (Restricted true 0);
    prf.prf_f i
  end
  else ()

let matches_map_group_map_group_cons_one_no_repeats
   #b (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst x)))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b
    end /\
    matches_map_group (map_group_cons_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> false
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))
= match Cbor.list_ghost_assoc k x with
  | None -> matches_map_group_map_group_cons_one_none k ty g x
  | Some y ->
    Classical.move_requires (matches_map_group_map_group_cons_restricted_some_ty k ty true g) x;
    if ty y
    then
      let x' = List.Tot.filter (map_key_neq _ k) x in
      matches_map_group_conv g x' (map_group_cons_one (map_group_entry_for k ty) true g) x
        (fun prf -> matches_map_group_map_group_cons_restricted_some_no_repeats_intro k ty true g x prf)
        (fun prf -> matches_map_group_map_group_cons_restricted_some_no_repeats_elim k ty true g x prf)
    else ()

let rec list_sorted_filter
  (#t1: Type)
  (key_order: t1 -> t1 -> bool {
    forall x y z . (key_order x y /\ key_order y z) ==> key_order x z
  })
  (f: t1 -> bool)
  (l: list t1)
: Lemma
  (requires (
    List.Tot.sorted key_order l
  ))
  (ensures (
    List.Tot.sorted key_order (List.Tot.filter f l)
  ))
= match l with
  | [] -> ()
  | a :: q ->
    list_sorted_filter key_order f q;
    if f a
    then begin
      Cbor.list_sorted_cons_elim key_order a q;
      list_for_all_filter_invariant (key_order a) f q
    end
    else ()

let list_sorted_deterministically_encoded_cbor_map_key_order_filter
  (#t: Type)
  (f: (Cbor.raw_data_item & t) -> bool)
  (l: list (Cbor.raw_data_item & t))
: Lemma
  (requires (
    List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) l
  ))
  (ensures (
    List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) (List.Tot.filter f l)
  ))
  [SMTPat (List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) (List.Tot.filter f l))]
= list_sorted_filter (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) f l

let matches_map_group_map_group_cons_zero_or_one_deterministically_encoded_cbor_map_key_order
  #b k ty g x
= Cbor.list_sorted_map_entry_order_deterministically_encoded_cbor_map_key_order_no_repeats x;
  matches_map_group_map_group_cons_zero_or_one_no_repeats k ty g x

let matches_map_group_map_group_cons_one_deterministically_encoded_cbor_map_key_order
  #b k ty g x
= Cbor.list_sorted_map_entry_order_deterministically_encoded_cbor_map_key_order_no_repeats x;
  matches_map_group_map_group_cons_one_no_repeats k ty g x
