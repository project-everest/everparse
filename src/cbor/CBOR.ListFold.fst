module CBOR.ListFold

let op_comm
  (#accu #t: Type)
  (f: accu -> t -> accu)
: Tot prop
= forall a x1 x2 . f (f a x1) x2 == f (f a x2) x1

let rec fold_comm
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
    fold_comm f (f a h1) q1 (h2 :: q2);
    assert (x == List.Tot.fold_left f (f a h1) (h2 :: List.Tot.append q2 q1));
    assert (f (f a h1) h2 == f (f a h2) h1);
    assert (x == List.Tot.fold_left f (f a h2) (h1 :: List.Tot.append q2 q1));
    fold_comm f (f (f a h2) h1) q2 q1;
    assert (x == List.Tot.fold_left f (f a h2) (l1 `List.Tot.append` q2));
    fold_comm f (f a h2) l1 q2;
    assert (x == List.Tot.fold_left f a (l2 `List.Tot.append` l1))

let op_idem
  (#accu #t: Type)
  (f: accu -> t -> accu)
: Tot prop
= forall a x . f (f a x) x == f a x

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

open FStar.Mul

let ghost_neq (#t: Type) (l2: t) : Tot (Ghost.erased (t -> bool)) =
  FStar.Ghost.Pull.pull (fun l1 -> FStar.StrongExcludedMiddle.strong_excluded_middle (~ (l1 == l2)))

let ghost_neq_equiv (#t: Type) (l2: t) (l1: t) : Lemma
  (Ghost.reveal (ghost_neq l2) l1 == true <==> (~ (l1 == l2)))
//  [SMTPat (Ghost.reveal (ghost_neq l2) l1)]
= ()

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
  fold_comm f a ll (h :: lr);
  fold_comm f (f a h) lr ll;
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
let rec fold_ext
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
    fold_ext f (f a h) (List.Tot.filter (ghost_neq h) q) (List.Tot.filter (ghost_neq h) q')
