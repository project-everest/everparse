module CDDL.Spec.GhostMap
module FE = FStar.FunctionalExtensionality

let ghost_map'
  (key value: Type u#a)
: Type u#a
= FE.restricted_g_t key (fun _ -> option value)

let ghost_map_mem' (#key #value: Type) (kv: (key & value)) (f: ghost_map' key value) : Tot prop =
  f (fst kv) == Some (snd kv)

let ghost_map_nil' (#key #value: Type u#a) : ghost_map' key value =
  FE.on_dom_g _ (fun _ -> None)

let ghost_map_cons' (#key #value: Type u#a) (k: key) (v: value) (g: ghost_map' key value) : ghost_map' key value =
  FE.on_dom_g _ (fun k' -> if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k') then Some v else g k')

let ghost_map_of_list'
  (#key #value: Type0)
  (l: list (key & value))
: Tot (ghost_map' key value)
= FE.on_dom_g _ (fun k' -> Cbor.list_ghost_assoc k' l)

let ghost_map_pred
  (#key #value: Type0)
  (g: ghost_map' key value)
  (l: list (key & value))
: Tot prop
= g == ghost_map_of_list' l

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

let ghost_neq (#t: Type) (l2: t) : Tot (Ghost.erased (t -> bool)) =
  FStar.Ghost.Pull.pull (fun l1 -> FStar.StrongExcludedMiddle.strong_excluded_middle (~ (l1 == l2)))

let ghost_neq_equiv (#t: Type) (l2: t) (l1: t) : Lemma
  (Ghost.reveal (ghost_neq l2) l1 <==> (~ (l1 == l2)))
//  [SMTPat (Ghost.reveal (ghost_neq l2) l1)]
= ()

let ghost_key_neq (#key #value: Type) (k: key) : Tot (Ghost.erased (key & value -> bool)) =
  FStar.Ghost.Pull.pull (fun l1 -> FStar.StrongExcludedMiddle.strong_excluded_middle (~ (fst l1 == k)))

let ghost_key_neq_equiv (#key #value: Type) (k: key) (kv: (key & value)) : Lemma
  (Ghost.reveal (ghost_key_neq k) kv == true <==> ~ (fst kv == k))
= ()

#restart-solver
let rec list_ghost_assoc_filter_neq
  (#key #value: Type)
  (k: key)
  (l: list (key & value))
  (k': key)
: Lemma
  (ensures (Cbor.list_ghost_assoc k' (List.Tot.filter (ghost_key_neq k) l) == (if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k') then None else Cbor.list_ghost_assoc k' l)))
  (decreases l)
= match l with
  | [] ->
    assert_norm (List.Tot.filter (ghost_key_neq #key #value k) [] == []);
    assert_norm (Cbor.list_ghost_assoc #key #value k' [] == None)
  | k2v2 :: q ->
    let (k2, v2) = k2v2 in
    ghost_key_neq_equiv k k2v2;
    assert (Ghost.reveal (ghost_key_neq k) k2v2 == true <==> ~ (k2 == k));
    list_ghost_assoc_filter_neq k q k'

#restart-solver
let rec prune_assoc
  (#key #value: Type)
  (l: list (key & value))
: Ghost (list (key & value))
    (requires True)
    (ensures (fun l' ->
      List.Tot.length l >= List.Tot.length l' /\
      List.Tot.no_repeats_p (List.Tot.map fst l') /\
      (forall k . Cbor.list_ghost_assoc k l' == Cbor.list_ghost_assoc k l)
    ))
= match l with
  | [] ->
    assert_norm (forall k . Cbor.list_ghost_assoc #key #value k [] == None);
    assert_norm (List.Tot.no_repeats_p (List.Tot.map (fst #key #value) []));
    []
  | (k, v) :: l' ->
    let res =
      (k, v) :: List.Tot.filter (ghost_key_neq k) (prune_assoc l')
    in
    Classical.forall_intro (list_ghost_assoc_filter_neq k (prune_assoc l'));
    list_no_repeats_filter (ghost_key_neq k) (prune_assoc l');
    list_memP_map fst (List.Tot.filter (ghost_key_neq k) (prune_assoc l')) k;
    Classical.forall_intro (ghost_key_neq_equiv #key #value k);
    assert (~ (List.Tot.memP k (List.Tot.map fst (List.Tot.filter (ghost_key_neq k) (prune_assoc l')))));
    res

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

#restart-solver
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

let list_memP_equiv_map_no_repeats
  (#key #value: Type)
  (l1 l2: list (key & value))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l1) /\
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2) /\
    List.Tot.length l1 >= List.Tot.length l2
  ))
  (ensures (
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.no_repeats_p (List.Tot.map fst l2)
  ))
= Classical.forall_intro (list_memP_map fst l1);
  Classical.forall_intro (list_memP_map fst l2);
  list_memP_equiv_no_repeats (List.Tot.map fst l1) (List.Tot.map fst l2)

let rec list_ghost_assoc_memP
  (#key #value: Type)
  (l: list (key & value))
  (k: key)
: Lemma
  (ensures (Some? (Cbor.list_ghost_assoc k l) <==> List.Tot.memP k (List.Tot.map fst l)))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> list_ghost_assoc_memP q k

let list_ghost_assoc_equiv_no_repeats // variant of the pigeon-hole principle, but with assoc instead of mem
  (#key #value: Type)
  (l1 l2: list (key & value))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l1) /\
    (forall x . Cbor.list_ghost_assoc x l1 == Cbor.list_ghost_assoc x l2) /\
    List.Tot.length l1 >= List.Tot.length l2
  ))
  (ensures (
    List.Tot.length l1 == List.Tot.length l2 /\
    List.Tot.no_repeats_p (List.Tot.map fst l2)
  ))
= Classical.forall_intro (list_ghost_assoc_memP l1);
  Classical.forall_intro (list_ghost_assoc_memP l2);
  list_memP_equiv_no_repeats (List.Tot.map fst l1) (List.Tot.map fst l2)

let rec list_ghost_assoc_memP_strong
  (#key #value: Type)
  (k: key)
  (v: value)
  (l: list (key & value))
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (ensures (Cbor.list_ghost_assoc k l == Some v <==> List.Tot.memP (k, v) l))
  (decreases l)
= match l with
  | [] -> ()
  | (k', v') :: q ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then Classical.forall_intro (list_memP_map fst q)
    else list_ghost_assoc_memP_strong k v q

let list_ghost_assoc_memP_strong_curry
  (#key #value: Type)
  (l: list (key & value))
  (kv: (key * value))
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (ensures (Cbor.list_ghost_assoc (fst kv) l == Some (snd kv) <==> List.Tot.memP kv l))
= list_ghost_assoc_memP_strong (fst kv) (snd kv) l

let ghost_map_length_pred
  (#key #value: Type)
  (g: ghost_map' key value)
  (len: nat)
  (l: list (key & value))
: Tot prop
= ghost_map_pred g l /\
  List.Tot.no_repeats_p (List.Tot.map fst l) /\
  len == List.Tot.length l

let ghost_map_length_unique
  (#key #value: Type)
  (g: ghost_map' key value)
  (len1 len2: nat)
  (l1 l2: list (key & value))
: Lemma
  (requires (
    ghost_map_length_pred g len1 l1 /\
    ghost_map_length_pred g len2 l2
  ))
  (ensures (
    len1 == len2
  ))
= assert (forall k . ghost_map_of_list' l1 k == ghost_map_of_list' l2 k);
  assert (forall k . ghost_map_of_list' l1 k == Cbor.list_ghost_assoc k l1);
  assert (forall k . Cbor.list_ghost_assoc k l1 == Cbor.list_ghost_assoc k l2);
  if List.Tot.length l1 >= List.Tot.length l2
  then list_ghost_assoc_equiv_no_repeats l1 l2
  else list_ghost_assoc_equiv_no_repeats l2 l1

let ghost_map key value = (g: ghost_map' key value { exists l . ghost_map_pred g l })

let ghost_map_elim_weak
  (#key #value: Type)
  (g: ghost_map key value)
: Ghost (list (key & value))
    (requires True)
    (ensures fun l -> ghost_map_pred g l)
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun l -> ghost_map_pred g l)

let ghost_map_elim_strong
  (#key #value: Type)
  (g: ghost_map key value)
: Ghost (list (key & value))
    (requires True)
    (ensures fun l -> ghost_map_pred g l /\
      List.Tot.no_repeats_p (List.Tot.map fst l)
    )
= let l1 = ghost_map_elim_weak g in
  let l2 = prune_assoc l1 in
  assert (FE.feq_g (ghost_map_of_list' l1) (ghost_map_of_list' l2));
  l2

let apply_ghost_map m k = m k

let ghost_map_ext m1 m2 =
  assert (FE.feq_g m1 m2)

let ghost_map_equiv' (#key #value: Type) (f1 f2: ghost_map' key value) : Lemma
  (requires (forall kv . ghost_map_mem' kv f1 <==> ghost_map_mem' kv f2))
  (ensures f1 == f2)
= let prf x y : Lemma (f1 x == Some y <==> f2 x == Some y) =
    let xy = (x, y) in
    assert (ghost_map_mem' xy f1 <==> ghost_map_mem' xy f2);
    ()
  in
  Classical.forall_intro_2 prf;
  assert (FE.feq_g f1 f2)

let ghost_map_equiv f1 f2 =
  ghost_map_equiv' f1 f2

let ghost_map_intro
  (#key #value: Type)
  (g: ghost_map' key value)
  (l: list (key & value))
: Pure (ghost_map key value)
    (requires
//      List.Tot.no_repeats_p (List.Tot.map fst l) /\
      ghost_map_of_list' l `FE.feq_g` g
    )
    (ensures fun _ -> True)
= g

let ghost_map_empty #key #value =
  ghost_map_intro ghost_map_nil' []

let apply_ghost_map_empty k = ()

let ghost_map_singleton k v =
  ghost_map_intro
    (ghost_map_cons' k v ghost_map_nil')
    [k, v]

let apply_ghost_map_singleton k v k' = ()

let ghost_map_union m1 m2 =
  let l1 = ghost_map_elim_weak m1 in
  let l2 = ghost_map_elim_weak m2 in
  ghost_map_of_list' (l1 `List.Tot.append` l2)

let apply_ghost_map_union m1 m2 k =
  let l1 = ghost_map_elim_weak m1 in
  let l2 = ghost_map_elim_weak m2 in
  Cbor.list_ghost_assoc_append k l1 l2

let ghost_map_length m =
  List.Tot.length (ghost_map_elim_strong m)

let ghost_map_length_intro
  (#key #value: Type)
  (l: list (key & value))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l)
  ))
  (ensures (
    ghost_map_length (ghost_map_of_list' l) == List.Tot.length l
  ))
= let l' = ghost_map_elim_strong (ghost_map_of_list' l) in
  ghost_map_length_unique (ghost_map_of_list' l) (List.Tot.length l) (List.Tot.length l') l l'

let ghost_map_length_is_empty m =
  let l = ghost_map_elim_strong m in
  Classical.forall_intro (Classical.move_requires (list_ghost_assoc_memP_strong_curry l));
  assert (m `ghost_map_equal` ghost_map_empty <==> l == [])

let ghost_map_length_singleton k v =
  ghost_map_length_intro [k, v]

let ghost_map_length_disjoint_union
  m1 m2
= let l1 = ghost_map_elim_strong m1 in
  let l2 = ghost_map_elim_strong m2 in
  List.Tot.append_length l1 l2;
  ghost_map_disjoint_mem_union' m1 m2 ();
  List.Tot.map_append fst l1 l2;
  Classical.forall_intro (list_ghost_assoc_memP l1);
  Classical.forall_intro (list_ghost_assoc_memP l2);
  assert (forall k . ~ (List.Tot.memP k (List.Tot.map fst l1) /\ List.Tot.memP k (List.Tot.map fst l2)));
  List.Tot.no_repeats_p_append (List.Tot.map fst l1) (List.Tot.map fst l2);
  ghost_map_length_intro (l1 `List.Tot.append` l2);
  Classical.forall_intro (fun k -> Cbor.list_ghost_assoc_append k l1 l2);
  ghost_map_ext (ghost_map_union m1 m2) (ghost_map_of_list' (l1 `List.Tot.append` l2))

let ghost_map_filter'
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map' key value)
: Tot (ghost_map' key value)
= FE.on_dom_g _ (fun k ->
    match m k with
    | None -> None
    | Some v -> if f (k, v) then Some v else None
  )

let list_filter_memP
  (#t: Type)
  (f: t -> bool)
  (l: list t)
  (x: t)
: Lemma
  (List.Tot.memP x (List.Tot.filter f l) <==> (List.Tot.memP x l /\ f x))
= ()

let ghost_map_filter_of_list'
  (#key #value: Type)
  (f: _ -> bool)
  (l: list (key & value))
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (ensures (ghost_map_filter' f (ghost_map_of_list' l) == ghost_map_of_list' (List.Tot.filter f l)))
= Classical.forall_intro (Classical.move_requires (list_ghost_assoc_memP_strong_curry l));
  Classical.forall_intro (list_filter_memP f l);
  list_no_repeats_filter f l;
  Classical.forall_intro (Classical.move_requires (list_ghost_assoc_memP_strong_curry (List.Tot.filter f l)));
  ghost_map_equiv'
    (ghost_map_filter' f (ghost_map_of_list' l))
    (ghost_map_of_list' (List.Tot.filter f l))

let ghost_map_filter f m =
  let l = ghost_map_elim_strong m in
  let f' = FStar.Ghost.Pull.pull f in
  ghost_map_filter_of_list' f' l;
  ghost_map_equiv'
    (ghost_map_filter' f' (ghost_map_of_list' l))
    (ghost_map_filter' f (ghost_map_of_list' l));
  ghost_map_intro (ghost_map_filter' f m) (List.Tot.filter f' l)

let apply_ghost_map_filter
  f m k
= ()

let ghost_map_of_list
  l
= ghost_map_of_list' l

let apply_ghost_map_of_list'
  (#key #value: Type)
  (l: list (key & value))
  (k: key)
: Lemma
  (apply_ghost_map (ghost_map_of_list l) k == Cbor.list_ghost_assoc k l)
= ()

let apply_ghost_map_of_list
  l k
= apply_ghost_map_of_list' l k

let ghost_map_of_list_singleton
  kv
= ()

let ghost_map_of_list_append
  l1 l2
= Classical.forall_intro (fun k -> Cbor.list_ghost_assoc_append k l1 l2);
  ghost_map_ext
    (ghost_map_of_list l1 `ghost_map_union` ghost_map_of_list l2)
    (ghost_map_of_list (l1 `List.Tot.append` l2))

let ghost_map_of_list_mem
  l x
= list_ghost_assoc_memP_strong_curry l x

let ghost_map_filter_of_list
  f l
= ghost_map_filter_of_list' f l
  
let ghost_map_length_of_list
  l
= let prf1 () : Lemma
    (requires ghost_map_length (ghost_map_of_list l) == List.Tot.length l)
    (ensures List.Tot.no_repeats_p (List.Tot.map fst l))
  = let l' = ghost_map_elim_strong (ghost_map_of_list l) in
    Classical.forall_intro (apply_ghost_map_of_list' l);
    Classical.forall_intro (apply_ghost_map_of_list' l');
    list_ghost_assoc_equiv_no_repeats l' l
  in
  let prf2 () : Lemma
    (requires List.Tot.no_repeats_p (List.Tot.map fst l))
    (ensures ghost_map_length (ghost_map_of_list l) == List.Tot.length l)
  = let l' = ghost_map_elim_strong (ghost_map_of_list l) in
    ghost_map_length_unique (ghost_map_of_list l) (List.Tot.length l) (List.Tot.length l') l l'
  in
  Classical.move_requires prf1 ();
  Classical.move_requires prf2 ()

let ghost_map_sub
  m1 m2
= let m3 = ghost_map_filter (fun kv -> not (FStar.StrongExcludedMiddle.strong_excluded_middle (ghost_map_mem kv m2))) m1 in
  assert (ghost_map_disjoint m2 m3);
  ghost_map_disjoint_mem_union' m2 m3 ();
  ghost_map_equiv (m2 `ghost_map_union` m3) m1;
  m3
