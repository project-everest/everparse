module CBOR.Spec.FiniteMap

open FStar.FunctionalExtensionality

let rec list_fold_comm
  (#accu #t: Type)
  (f: accu -> t -> accu { op_comm f })
  (a: accu)
  (l1 l2: list t)
: Lemma
  (ensures (List.Tot.fold_left f a (List.Tot.append l1 l2) == List.Tot.fold_left f a (List.Tot.append l2 l1)))
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  | [], _ -> List.Tot.append_l_nil l2
  | _, [] -> List.Tot.append_l_nil l1
  | h1 :: q1, h2 :: q2 ->
    let x = List.Tot.fold_left f a (List.Tot.append l1 l2) in
    list_fold_comm f (f a h1) q1 (h2 :: q2);
    assert (x == List.Tot.fold_left f (f a h1) (h2 :: List.Tot.append q2 q1));
    assert (f (f a h1) h2 == f (f a h2) h1);
    assert (x == List.Tot.fold_left f (f a h2) (h1 :: List.Tot.append q2 q1));
    list_fold_comm f (f (f a h2) h1) q2 q1;
    assert (x == List.Tot.fold_left f (f a h2) (l1 `List.Tot.append` q2));
    list_fold_comm f (f a h2) l1 q2;
    assert (x == List.Tot.fold_left f a (l2 `List.Tot.append` l1))

open FStar.Mul

let rec list_filter_append
  (#t: Type)
  (f: t -> bool)
  (l1 l2: list t)
: Lemma
  (ensures List.Tot.filter f (l1 `List.Tot.append` l2) == List.Tot.filter f l1 `List.Tot.append` List.Tot.filter f l2)
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_filter_append f q l2

let ghost_neq (#t: Type) (l2: t) : Tot (Ghost.erased (t -> bool)) =
  FStar.Ghost.Pull.pull (fun l1 -> FStar.StrongExcludedMiddle.strong_excluded_middle (~ (l1 == l2)))

let ghost_neq_equiv (#t: Type) (l2: t) (l1: t) : Lemma
  (Ghost.reveal (ghost_neq l2) l1 <==> (~ (l1 == l2)))
//  [SMTPat (Ghost.reveal (ghost_neq l2) l1)]
= ()

#restart-solver
let rec filter_ghost_neq_not_memP
  (#t: Type)
  (h: t)
  (l: list t)
: Lemma
  (requires (~ (List.Tot.memP h l)))
  (ensures (List.Tot.filter (ghost_neq h) l == l))
= match l with
  | [] -> assert_norm (List.Tot.filter (ghost_neq h) [] == [])
  | a :: q ->
    assert_norm (List.Tot.filter (ghost_neq h) (a :: q) == (if Ghost.reveal (ghost_neq h) a then a :: List.Tot.filter (ghost_neq h) q else List.Tot.filter (ghost_neq h) q));
    assert (List.Tot.memP h l <==> (a == h \/ List.Tot.memP h q));
    ghost_neq_equiv h a;
    assert (Ghost.reveal (ghost_neq h) a == true <==> (~ (a == h)));
    assert (~ (a == h));
    assert (Ghost.reveal (ghost_neq h) a == true);
    filter_ghost_neq_not_memP h q

let rec memP_filter_ghost_neq'
  (#t: Type)
  (h: t)
  (l: list t)
  (x: t)
: Lemma
  (ensures (List.Tot.memP x (List.Tot.filter (ghost_neq h) l) <==> List.Tot.memP x l /\ (~ (x == h))))
  (decreases l)
= match l with
  | [] -> assert_norm (List.Tot.filter (ghost_neq h) [] == [])
  | a :: q ->
    assert_norm (List.Tot.filter (ghost_neq h) (a :: q) == (if Ghost.reveal (ghost_neq h) a then a :: List.Tot.filter (ghost_neq h) q else List.Tot.filter (ghost_neq h) q));
    memP_filter_ghost_neq' h q x;
    ghost_neq_equiv h a

let memP_filter_ghost_neq
  (#t: Type)
  (h: t)
  (l: list t)
: Lemma
  (ensures forall x . (List.Tot.memP x (List.Tot.filter (ghost_neq h) l) <==> List.Tot.memP x l /\ (~ (x == h))))
= Classical.forall_intro (memP_filter_ghost_neq' h l)

let rec list_memP_extract
  (#t: Type)
  (x: t)
  (l: list t)
: Ghost (list t & list t)
  (requires FStar.List.Tot.memP x l)
  (ensures fun (ll, lr) ->
    l == ll `List.Tot.append` (x :: lr)
  )
= let a :: q = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (a == x)
  then ([], q)
  else
    let (ll, lr) = list_memP_extract x q in
    (a :: ll, lr)

#restart-solver
let fold_filter_memP
  (#accu #t: Type)
  (f: accu -> t -> accu { op_comm f })
  (a: accu)
  (h: t)
  (l: list t)
: Ghost (list t)
  (requires (List.Tot.memP h l))
  (ensures (fun q ->
    List.Tot.fold_left f a l == List.Tot.fold_left f (f a h) q /\
    List.Tot.length q < List.Tot.length l /\
    (forall x . List.Tot.memP x l <==> (x == h \/ List.Tot.memP x q)) /\
    List.Tot.filter (ghost_neq h) l == List.Tot.filter (ghost_neq h) q
  ))
= 
  let (ll, lr) = list_memP_extract h l in
  List.Tot.append_length ll (h :: lr);
  List.Tot.append_memP_forall ll (h :: lr);
  list_fold_comm f a ll (h :: lr);
  list_fold_comm f (f a h) lr ll;
  List.Tot.append_length ll lr;
  List.Tot.append_memP_forall ll lr;
  list_filter_append (ghost_neq h) ll (h :: lr);
  assert (List.Tot.filter (ghost_neq h) l == List.Tot.filter (ghost_neq h) ll `List.Tot.append` List.Tot.filter (ghost_neq h) lr);
  assert (List.Tot.filter (ghost_neq h) (h :: lr) == List.Tot.filter (ghost_neq h) lr);
  assert (List.Tot.filter (ghost_neq h) l == List.Tot.filter (ghost_neq h) ll `List.Tot.append` List.Tot.filter (ghost_neq h) lr);
  list_filter_append (ghost_neq h) ll lr;
  List.Tot.append ll lr

let rec fold_filter_ghost_neq (#accu #t: Type)
  (f: accu -> t -> accu { op_comm f /\ op_idem f })
  (a: accu)
  (h: t)
  (l: list t)
: Lemma
  (ensures (List.Tot.fold_left f (f a h) l == List.Tot.fold_left f (f a h) (List.Tot.filter (ghost_neq h) l)))
  (decreases (List.Tot.length l))
= if FStar.StrongExcludedMiddle.strong_excluded_middle (List.Tot.memP h l)
  then begin
    let q = fold_filter_memP f (f a h) h l in
    fold_filter_ghost_neq f a h q
  end
  else filter_ghost_neq_not_memP h l

let rec list_length_filter
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (List.Tot.length (List.Tot.filter f l) <= List.Tot.length l)
  [SMTPat (List.Tot.length (List.Tot.filter f l))]
= match l with
  | [] -> ()
  | _ :: q -> list_length_filter f q

#restart-solver
let rec list_fold_ext
  (#accu #t: Type)
  (f: accu -> t -> accu { op_comm f /\ op_idem f })
  (a: accu)
  (l1 l2: list t)
: Lemma
  (requires (
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2)
  ))
  (ensures (List.Tot.fold_left f a l1 == List.Tot.fold_left f a l2))
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1 with
  | [] -> ()
  | h :: q ->
    let q' = fold_filter_memP f a h l2 in
    fold_filter_ghost_neq f a h q;
    fold_filter_ghost_neq f a h q';
    list_length_filter (ghost_neq h) q';
    memP_filter_ghost_neq h q;
    memP_filter_ghost_neq h q';
    list_fold_ext f (f a h) (List.Tot.filter (ghost_neq h) q) (List.Tot.filter (ghost_neq h) q')

let list_fold_ext'
  (#accu #t: Type)
  (f: accu -> t -> accu { op_comm f /\ op_idem f })
  (a: accu)
  (l1 l2: list t)
: Lemma
  (ensures
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2) ==>
    List.Tot.fold_left f a l1 == List.Tot.fold_left f a l2
  )
= Classical.move_requires (list_fold_ext f a l1) l2

let map (t u: Type) : Type = t ^-> option u

let map_get (#t #u: Type) (x: t) (s: map t u) : option u = s x

let map_equal
  (#t #u: Type)
  (s1 s2: map t u)
: Tot prop
= forall x . map_get x s1 == map_get x s2

let map_equal_eq_intro
  (#t #u: Type)
  (s1 s2: map t u)
: Lemma
  (requires map_equal s1 s2)
  (ensures s1 == s2)
= assert (feq s1 s2)

let map_equal_eq
  (#t #u: Type)
  (s1 s2: map t u)
: Lemma
  (map_equal s1 s2 <==> s1 == s2)
  [SMTPat (map_equal s1 s2)]
= Classical.move_requires (map_equal_eq_intro s1) s2

let fmap' (t u: Type) : Type =
  (s: map t u { exists (l: list t) . forall (x: t) . List.Tot.memP x l <==> Some? (s x) })

let map_included (#t #u: Type) (s1 s2: t -> option u) : Tot prop =
  forall (elt: t) . begin match s1 elt with
  | None -> True
  | g -> g == s2 elt
  end

let included_elem_test_codom (#t #u: Type) (x: t -> option u) (y: t -> option u) : Type =
  (z: bool { z == true <==> map_included x y})

let included_elem_test (#t #u: Type) (x: t -> option u) : Type =
  restricted_t (t -> option u) (included_elem_test_codom x)

noeq
type fmap_fold_dom
  (t: Type u#a) (token: universe_token u#c)
: Type u#(max a (1 + c))
= {
  accu: Type u#c;
  f: (f: (accu -> t -> accu) { op_comm f /\ op_idem f });
  a: accu;
}

let fmap_fold_codom
  (#t: Type u#a) (#u: Type u#b) (#token: universe_token u#c) (s: t -> option u) (x: fmap_fold_dom t token) : Type u#c =
  (a': x.accu { forall l . (forall x . List.Tot.memP x l <==> Some? (s x)) ==> a' == List.Tot.fold_left x.f x.a l })

noeq
type fmap (t: Type u#a) (u: Type u#b) (token: universe_token u#c) : Type u#(max a b (1 + c)) = {
  s: fmap' t u;
  test: included_elem_test s;
  fold: restricted_t (fmap_fold_dom t token) (fmap_fold_codom s);
}

let fmap_eq (#t #u: Type) #token : eq_test (fmap t u token) =
  (fun (s1: fmap t u token) -> fun (s2: fmap t u token) ->
    let res : bool = s1.test s2.s && s2.test s1.s in
    if res
    then begin
      assert (s1.s `map_equal` s2.s);
      assert (feq s1.test s2.test);
      assert (feq s1.fold s2.fold);
      true
    end
    else false
  )

let fmap_fold_codom'
  (#t: Type u#a) (l: list t) (#token: universe_token u#c) (x: fmap_fold_dom t token) : Type u#c =
  (a': x.accu { a' == List.Tot.fold_left x.f x.a l })

let fmap_intro
  (#t #u: Type)
  (#token: universe_token)
  (s: t -> Tot (option u))
  (test: (t -> option u) -> Tot bool)
  (l: Ghost.erased (list t))
  (fold: (x: fmap_fold_dom t token) -> fmap_fold_codom' l x)
: Pure (fmap t u token)
    (requires (
      (forall (x: t) . List.Tot.memP x l <==> Some? (s x)) /\
      (forall (s': t -> option u) . test s' <==>  map_included s s')
    ))
    (ensures (fun _ -> True))
= Classical.exists_intro (fun (l: list t) -> forall (x: t) . List.Tot.memP x l <==>  Some? (s x) ) l;
  let s0 : fmap' t u = on_dom t s in
  {
    s = s0;
    test = on_dom (t -> option u) #(included_elem_test_codom s0) (fun (s': t -> option u) -> test s');
    fold = on_dom (fmap_fold_dom t token) #(fmap_fold_codom s0) (fun x -> 
      Classical.forall_intro (list_fold_ext' x.f x.a l);
      fold x
    );
  }

let fmap_elim
  (#t #u: Type)
  (#token: _)
  (s: fmap t u token)
: Ghost (list t)
    (requires True)
    (ensures (fun l -> forall (x: t) . List.Tot.memP x l <==> Some? (s.s x)))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun (l: list t) -> forall (x: t) . List.Tot.memP x l <==> Some? (s.s x ))

let get (#t #u: Type) (#token: _) (x: t) (s: fmap t u token) : Tot (option u) = s.s x

let domain s = fmap_elim s

let equal_eq_intro
  (#t #u: Type) (#token: _)
  (s1 s2: fmap t u token)
: Lemma
  (requires equal s1 s2)
  (ensures s1 == s2)
= assert (feq s1.s s2.s);
  assert (feq s1.test s2.test);
  assert (feq s1.fold s2.fold)

let equal_eq
  (#t #u: Type) #token
  (s1 s2: fmap t u token)
: Lemma
  (equal s1 s2 <==> s1 == s2)
  [SMTPat (equal s1 s2)]
= Classical.move_requires (equal_eq_intro s1) s2

let fold
  f a s
= Classical.forall_intro (list_fold_ext' f a (domain s));
  s.fold { accu = _; f = f; a = a }

let empty (t u: Type) token : Pure (fmap t u token)
  (requires True)
  (ensures (fun s -> forall x . None? (get x s)))
=
  fmap_intro (fun _ -> None) (fun _ -> true) [] (fun x -> x.a)

let singleton (#t #u: Type) token (x: t) (elt: u) (eq: eq_elem_test x) (equ: eq_elem_test elt) : Pure (fmap t u token)
  (requires True)
  (ensures (fun s -> get x s == Some elt /\ (forall y . (~ (x == y)) ==>  get y s == None)))
=
  fmap_intro (fun y' -> if eq y' then Some elt else None) (fun s' -> 
    match s' x with
    | None -> false
    | Some elt' -> equ elt')
  [x]
  (fun y -> y.f y.a x)

let union (#t #u: Type) #token (s1 s2: fmap t u token) : Pure (fmap t u token)
  (requires True)
  (ensures (fun s -> forall y . get y s == begin match get y s1 with
  | Some v -> Some v
  | _ -> get y s2
  end))
= let l1 = Ghost.hide (fmap_elim s1) in
  let l2 = Ghost.hide (fmap_elim s2) in
  Classical.forall_intro (FStar.List.Tot.append_memP l1 l2);
  fmap_intro (fun x -> match s1.s x with
  | None -> s2.s x
  | v -> v
  )
  (fun s' -> s1.test s' && s2.test (fun x' -> match s1.s x', s2.s x' with
  | Some _, Some v -> Some v
  | _ -> s' x'
  ))
  (l1 `List.Tot.append` l2)
  (fun x ->
    List.Tot.fold_left_append x.f l1 l2;
    s2.fold {x with a = s1.fold x}
  )

let rec list_memP_filter (#t: Type) (f: t -> bool) (l: list t) (x: t) : Lemma
  (ensures List.Tot.memP x (List.Tot.filter f l) <==> List.Tot.memP x l /\ f x)
  (decreases l)
  [SMTPat (List.Tot.memP x (List.Tot.filter f l))]
= match l with
  | [] -> ()
  | _ :: q -> list_memP_filter f q x

let rec list_filter_eq_length
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (List.Tot.length (List.Tot.filter f l) == List.Tot.length l))
  (ensures (List.Tot.filter f l == l))
= match l with
  | [] -> ()
  | a :: q -> list_length_filter f q; list_filter_eq_length f q

let rec list_memP_equiv_no_repeats // this is actually some form of the pigeon-hole principle
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (requires (
    List.Tot.no_repeats_p l1 /\
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2) /\
    List.Tot.length l1 >= List.Tot.length l2
  ))
  (ensures (
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.no_repeats_p l2
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a :: q ->
    let (ll, lr) = list_memP_extract a l2 in
    List.Tot.append_length ll (a :: lr);
    List.Tot.append_length ll lr;
    let q2 = List.Tot.filter (ghost_neq a) (ll `List.Tot.append` lr) in
    list_length_filter (ghost_neq a) (ll `List.Tot.append` lr);
    let prf
      (x: t)
    : Lemma
      (List.Tot.memP x q <==> List.Tot.memP x q2)
    = list_memP_filter (ghost_neq a) (ll `List.Tot.append` lr) x;
      List.Tot.append_memP ll lr x;
      List.Tot.append_memP ll (a :: lr) x;
      ghost_neq_equiv a x;
      assert (Ghost.reveal (ghost_neq a) x <==> ~ (x == a));
      assert (List.Tot.memP x q2 <==> (List.Tot.memP x ll \/ List.Tot.memP x lr) /\ Ghost.reveal (ghost_neq a) x);
      assert (List.Tot.memP x q2 <==> (List.Tot.memP x ll \/ List.Tot.memP x lr) /\ ~ (x == a))
    in
    Classical.forall_intro prf;
    list_memP_equiv_no_repeats q q2;
    list_filter_eq_length (ghost_neq a) (ll `List.Tot.append` lr);
    assert (q2 == ll `List.Tot.append` lr);
    assert (List.Tot.no_repeats_p (a :: q2));
    List.Tot.no_repeats_p_append_permut [] [] ll [a] lr

#restart-solver
let rec list_no_repeats_filter
  (#key: Type)
  (f: key -> bool)
  (l: list key)
: Lemma
  (requires
    List.Tot.no_repeats_p l
  )
  (ensures
    List.Tot.no_repeats_p (List.Tot.filter f l)
  )
  [SMTPat (List.Tot.no_repeats_p (List.Tot.filter f l))]
= match l with
  | [] -> ()
  | k :: q ->
    list_no_repeats_filter f q

let rec prune_list
  (#key: Type)
  (l: list key)
: Ghost (list key)
    (requires True)
    (ensures (fun l' ->
      List.Tot.length l >= List.Tot.length l' /\
      List.Tot.no_repeats_p l' /\
      (forall k . List.Tot.memP k l' <==> List.Tot.memP k l)     ))
= match l with
  | [] -> []
  | k :: l' ->
    let res =
      k :: List.Tot.filter (ghost_neq k) (prune_list l')
    in
    list_no_repeats_filter (ghost_neq k) (prune_list l');
    Classical.forall_intro (ghost_neq_equiv #key k);
    res

let length
  (#t #u: Type)
  #token
  (s: fmap t u token)
: GTot nat
= let l = fmap_elim s in
  List.Tot.length (prune_list l)

let length_intro
  (#t #u: Type)
  #token
  (s: fmap t u token)
  (l: list t)
: Lemma
  (requires (
    List.Tot.no_repeats_p l /\
    (forall k . List.Tot.memP k l <==> Some? (get k s))
  ))
  (ensures (
    length s == List.Tot.length l
  ))
= let l0 = prune_list (fmap_elim s) in
  if List.Tot.length l0 >= List.Tot.length l
  then list_memP_equiv_no_repeats l0 l
  else list_memP_equiv_no_repeats l l0

let length_empty
  (t u: Type)
  token
: Lemma
  (length (empty t u token) == 0)
= length_intro (empty t u token) []

let length_singleton
  (#t #u: Type) token (x: t) (elt: u) (eq: eq_elem_test x) (equ: eq_elem_test elt)
: Lemma
  (length (singleton token x elt eq equ) == 1)
= length_intro (singleton token x elt eq equ) [x]

let length_disjoint_union
  (#t #u: Type) #token (s1 s2: fmap t u token)
: Lemma
  (requires (disjoint s1 s2))
  (ensures (
    length (union s1 s2) == length s1 + length s2
  ))
= let l1 = prune_list (fmap_elim s1) in
  let l2 = prune_list (fmap_elim s2) in
  Classical.forall_intro (FStar.List.Tot.append_memP l1 l2);
  List.Tot.no_repeats_p_append l1 l2;
  List.Tot.append_length l1 l2;
  length_intro (union s1 s2) (l1 `List.Tot.append` l2)
