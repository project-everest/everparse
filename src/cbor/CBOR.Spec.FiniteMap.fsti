module CBOR.Spec.FiniteMap

let eq_elem_test_codom (#t: Type) (x: t) (y: t) : Type =
  (z: bool { z == true <==> x == y })

let eq_elem_test (#t: Type) (x: t) : Type =
  (y: t) -> (eq_elem_test_codom x y)

let eq_test (t: Type) =
  (x: t) -> eq_elem_test x

noeq type universe_token : Type u#a =
| UniverseToken

let op_comm
  (#accu #t: Type)
  (f: accu -> t -> accu)
: Tot prop
= forall a x1 x2 . f (f a x1) x2 == f (f a x2) x1

let op_idem
  (#accu #t: Type)
  (f: accu -> t -> accu)
: Tot prop
= forall a x . f (f a x) x == f a x

val fmap (t: Type u#a) (u: Type u#b) (token: universe_token u#c) : Type u#(max a b (1 + c))

val fmap_eq (#t #u: Type) (#token: universe_token) : eq_test (fmap t u token)

val get (#t #u: Type) (#token: universe_token) (x: t) (s: fmap t u token) : Tot (option u)

val domain (#t: Type u#a) (#u: Type u#b) (#token: universe_token u#c) (s: fmap t u token) : Ghost (list t)
  (requires True)
  (ensures (fun l -> forall x . List.Tot.memP x l <==> Some? (get x s)))

let equal
  (#t #u: Type)
  (#token: universe_token)
  (s1 s2: fmap t u token)
: Tot prop
= forall x . get x s1 == get x s2

val equal_eq
  (#t #u: Type)
  (#token: universe_token)
  (s1 s2: fmap t u token)
: Lemma
  (equal s1 s2 <==> s1 == s2)
  [SMTPat (equal s1 s2)]

val list_fold_comm
  (#accu #t: Type)
  (f: accu -> t -> accu { op_comm f })
  (a: accu)
  (l1 l2: list t)
: Lemma
  (ensures (List.Tot.fold_left f a (List.Tot.append l1 l2) == List.Tot.fold_left f a (List.Tot.append l2 l1)))

val list_fold_ext
  (#accu #t: Type)
  (f: accu -> t -> accu { op_comm f /\ op_idem f })
  (a: accu)
  (l1 l2: list t)
: Lemma
  (requires (
    (forall x . List.Tot.memP x l1 <==> List.Tot.memP x l2)
  ))
  (ensures (List.Tot.fold_left f a l1 == List.Tot.fold_left f a l2))

val fold
  (#t: Type u#a)
  (#u: Type u#b)
  (#token: universe_token u#c)
  (#accu: Type u#c)
  (f: accu -> t -> accu { op_comm f /\ op_idem f })
  (a: accu)
  (s: fmap t u token)
: Pure accu
    (requires True)
    (ensures (fun a' -> a' == List.Tot.fold_left f a (domain s)))

val empty (t u: Type) (token: universe_token) : Pure (fmap t u token)
  (requires True)
  (ensures (fun s -> forall x . None? (get x s)))

val singleton (#t #u: Type) (token: universe_token) (x: t) (elt: u) (eq: eq_elem_test x) (equ: eq_elem_test elt) : Pure (fmap t u token)
  (requires True)
  (ensures (fun s -> get x s == Some elt /\ (forall y . (~ (x == y)) ==>  get y s == None)))

val union (#t #u: Type) (#token: universe_token) (s1 s2: fmap t u token) : Pure (fmap t u token)
  (requires True)
  (ensures (fun s -> forall y . get y s == begin match get y s1 with
  | Some v -> Some v
  | _ -> get y s2
  end))

val length
  (#t #u: Type)
  (#token: universe_token)
  (s: fmap t u token)
: GTot nat

val length_empty
  (t u: Type)
  (token: universe_token)
: Lemma
  (length (empty t u token) == 0)
  [SMTPat (length (empty t u token))]

val length_singleton
  (#t #u: Type) (token: universe_token) (x: t) (elt: u) (eq: eq_elem_test x) (equ: eq_elem_test elt)
: Lemma
  (length (singleton token x elt eq equ) == 1)
  [SMTPat (length (singleton token x elt eq equ))]

let disjoint
  (#t #u: Type)
  (#token: universe_token)
  (s1 s2: fmap t u token)
: Tot prop
= forall x . None? (get x s1) \/ None? (get x s2)

val length_disjoint_union
  (#t #u: Type) (#token: universe_token) (s1 s2: fmap t u token)
: Lemma
  (requires (disjoint s1 s2))
  (ensures (
    length (union s1 s2) == length s1 + length s2
  ))
  [SMTPat (length (union s1 s2))]
