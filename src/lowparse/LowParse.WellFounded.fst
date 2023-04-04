module LowParse.WellFounded

let rec fold_left_list
  (#t: Type)
  (l: list t)
  (#t': Type)
  (p: t' -> (x: t { x << l }) -> t')
  (init: t')
: Tot t'
= match l with
  | [] -> init
  | a :: q -> fold_left_list q p (p init a)

let rec fold_left_list_ext
  (#t: Type)
  (l: list t)
  (#t': Type)
  (p1: t' -> (x: t { x << l }) -> t')
  (p2: t' -> (x: t { x << l }) -> t')
  (prf:
    (accu: t') ->
    (x: t { x << l }) ->
    Lemma
    (p1 accu x == p2 accu x)
  )
  (init: t')
: Lemma
  (ensures (fold_left_list l p1 init == fold_left_list l p2 init))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    prf init a;
    let accu' = p1 init a in
    fold_left_list_ext q p1 p2 prf accu'

let forall_list_f
  (#t: Type)
  (l: list t)
  (p: (x: t { x << l }) -> bool)
  (init: bool)
  (a: t { a << l })
: Tot bool
= init && p a

let forall_list
  (#t: Type)
  (l: list t)
  (p: (x: t { x << l }) -> bool)
: Tot bool
= fold_left_list l (forall_list_f l p) true

let forall_list_ext
  (#t: Type)
  (l: list t)
  (p1: (x: t { x << l }) -> bool)
  (p2: (x: t { x << l }) -> bool)
  (prf:
    (x: t { x << l }) ->
    Lemma
    (p1 x == p2 x)
  )
: Lemma
  (forall_list l p1 == forall_list l p2)
= fold_left_list_ext l (forall_list_f l p1) (forall_list_f l p2) (fun _ x -> prf x) true

let rec fold_left_list_forall_list_aux
  (#t: Type)
  (l: list t)
  (p: (x: t { x << l }) -> bool)
  (init: bool)
: Lemma
  (ensures (fold_left_list l (forall_list_f l p) init ==
    (init && fold_left_list l (forall_list_f l p) true)
  ))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    fold_left_list_ext q (forall_list_f l p) (forall_list_f q p) (fun _ _ -> ()) (init && p a);
    fold_left_list_ext q (forall_list_f l p) (forall_list_f q p) (fun _ _ -> ()) true;
    fold_left_list_forall_list_aux q p (init && p a)

let forall_list_cons'
  (#t: Type)
  (l: list t)
  (a: t)
  (q: list t)
  (p: (x: t { x << a :: q }) -> bool)
: Lemma
  (requires (
    l == a :: q
  ))
  (ensures (
    a << a :: q /\
    q << a :: q /\
    forall_list (a :: q) p == (p a && forall_list q p)
  ))
  (decreases l)
= match l with
  | _ :: _ ->
  assert (a << a :: q);
  assert (q << a :: q);
  fold_left_list_ext q (forall_list_f (a :: q) p) (forall_list_f q p) (fun _ _ -> ()) (p a);
  fold_left_list_forall_list_aux q p (p a)

let forall_list_cons
  (#t: Type)
  (a: t)
  (q: list t)
  (p: (x: t { x << a :: q }) -> bool)
: Lemma
  (ensures (
    a << a :: q /\
    q << a :: q /\
    forall_list (a :: q) p == (p a && forall_list q p)
  ))
= forall_list_cons' (a :: q) a q p

#restart-solver

let rec forall_list_implies
  (#t: Type)
  (l: list t)
  (p1: (x: t { x << l }) -> bool)
  (p2: (x: t { x << l }) -> bool)
  (prf: 
    (x: t { x << l }) ->
    Lemma
    (requires (p1 x))
    (ensures (p2 x))
  )
: Lemma
  (requires (forall_list l p1))
  (ensures (forall_list l p2))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    forall_list_cons a q p1;
    forall_list_cons a q p2;
    prf a;
    forall_list_implies q p1 p2 prf
