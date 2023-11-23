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

let rec fold_left_list_correct
  (#t: Type)
  (#t': Type)
  (p: t' -> t -> t')
  (l: list t)
  (init: t')
: Lemma
  (ensures (fold_left_list l p init == List.Tot.fold_left p init l))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> fold_left_list_correct p q (p init a)

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

let rec forall_list_correct
  (#t: Type)
  (p: t -> bool)
  (l: list t)
: Lemma
  (ensures (forall_list l p == List.Tot.for_all p l))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    forall_list_cons a q p;
    forall_list_correct p q

let forall_list_f_weak
  (#t: Type)
  (p: t -> bool)
  (init: bool)
  (a: t)
: Tot bool
= init && p a

let rec for_all_fold_left_aux
  (#t: Type)
  (p: t -> bool)
  (init: bool)
  (l: list t)
: Lemma
  (ensures ((init && List.Tot.for_all p l) == List.Tot.fold_left (forall_list_f_weak p) init l))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    for_all_fold_left_aux p (init && p a) q

let for_all_fold_left
  (#t: Type)
  (p: t -> bool)
  (l: list t)
: Lemma
  (ensures (List.Tot.for_all p l == List.Tot.fold_left (forall_list_f_weak p) true l))
= for_all_fold_left_aux p true l

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

(* Combinators to compute with levels *)

let acc_level
  (#t0: Type)
  (l: t0)
  (#t: Type)
  (level: (x: t { x << l }) -> nat)
  (accu: nat)
  (x: t { x << l })
: Tot nat
= let n = level x in
  if n > accu then n else accu

let acc_level_pair
  (#t0: Type)
  (l: t0)
  (#t: Type)
  (level: (x: t { x << l }) -> nat)
  (accu: nat)
  (x: (t & t) { x << l })
= let (x1, x2) = x in
  acc_level l level (acc_level l level accu x1) x2

let rec fold_left_list_acc_level_ge_accu
  (#t: Type)
  (v: list t)
  (level: (x: t { x << v }) -> nat)
  (accu: nat)
: Lemma
  (ensures (fold_left_list v (acc_level v level) accu >= accu))
= match v with
  | [] -> ()
  | a :: q ->
    let accu' = acc_level v level accu a in
    fold_left_list_ext q (acc_level v level) (acc_level q level) (fun _ _ -> ()) accu';
    fold_left_list_acc_level_ge_accu q level accu'

let rec fold_left_list_acc_level_pair_ge_accu
  (#t: Type)
  (v: list (t & t))
  (level: (x: t { x << v }) -> nat)
  (accu: nat)
: Lemma
  (ensures (fold_left_list v (acc_level_pair v level) accu >= accu))
= match v with
  | [] -> ()
  | a :: q ->
    let accu' = acc_level_pair v level accu a in
    fold_left_list_ext q (acc_level_pair v level) (acc_level_pair q level) (fun _ _ -> ()) accu';
    fold_left_list_acc_level_pair_ge_accu q level accu'

let has_level
  (#t: Type)
  (level: (t -> nat))
  (n: nat)
  (d: t)
: Tot bool
= level d <= n

let pair_has_level
  (#t: Type)
  (level: (t -> nat))
  (n: nat)
  (d: (t & t))
: Tot bool
= let (d1, d2) = d in
  has_level level n d1 &&
  has_level level n d2

let rec fold_left_list_has_level_gen
  (#t: Type)
  (level: (t -> nat))
  (n: nat)
  (v: list t)
  (accu: nat)
: Lemma
  (requires (n >= fold_left_list v (acc_level v level) accu))
  (ensures (forall_list v (has_level level n)))
  (decreases v)
= match v with
  | [] -> ()
  | a :: q ->
    let accu' = acc_level v level accu a in
    forall_list_cons a q (has_level level n);
    fold_left_list_ext q (acc_level v level) (acc_level q level) (fun _ _ -> ()) accu';
    fold_left_list_acc_level_ge_accu q level accu';
    fold_left_list_has_level_gen level n q accu'

let fold_left_list_has_level
  (#t: Type)
  (level: t -> nat)
  (v: list t)
  (accu: nat)
: Lemma
  (forall_list v (has_level level (fold_left_list v (acc_level v level) accu)))
= fold_left_list_has_level_gen level (fold_left_list v (acc_level v level) accu) v accu

let rec fold_left_list_pair_has_level_gen
  (#t: Type)
  (level: t -> nat)
  (n: nat)
  (v: list (t & t))
  (accu: nat)
: Lemma
  (requires (n >= fold_left_list v (acc_level_pair v level) accu))
  (ensures (forall_list v (pair_has_level level n)))
  (decreases v)
= match v with
  | [] -> ()
  | a :: q ->
    let accu' = acc_level_pair v level accu a in
    forall_list_cons a q (pair_has_level level n);
    fold_left_list_ext q (acc_level_pair v level) (acc_level_pair q level) (fun _ _ -> ()) accu';
    fold_left_list_acc_level_pair_ge_accu q level accu';
    fold_left_list_pair_has_level_gen level n q accu'

let fold_left_list_pair_has_level
  (#t: Type)
  (level: t -> nat)
  (v: list (t & t))
  (accu: nat)
: Lemma
  (forall_list v (pair_has_level level (fold_left_list v (acc_level_pair v level) accu)))
= fold_left_list_pair_has_level_gen level (fold_left_list v (acc_level_pair v level) accu) v accu
