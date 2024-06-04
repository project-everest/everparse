module CBOR.Spec.FiniteSet

let eq_elem_test_codom (#t: Type) (x: t) (y: t) : Type =
  (z: bool { z == true <==> x == y })

let eq_elem_test (#t: Type) (x: t) : Type =
  (y: t) -> (eq_elem_test_codom x y)

let eq_test (t: Type) =
  (x: t) -> eq_elem_test x

val fset (t: Type u#a) : Type u#a

val fset_eq (#t: Type) : eq_test (fset t)

val mem (#t: Type) (x: t) (s: fset t) : Tot bool

let equal
  (#t: Type)
  (s1 s2: fset t)
: Tot prop
= forall x . mem x s1 <==> mem x s2

val equal_eq
  (#t: Type)
  (s1 s2: fset t)
: Lemma
  (equal s1 s2 <==> s1 == s2)
  [SMTPat (equal s1 s2)]

val empty (t: Type) : Pure (fset t)
  (requires True)
  (ensures (fun s -> forall x . ~ (mem x s)))

val singleton (#t: Type) (x: t) (eq: eq_elem_test x) : Pure (fset t)
  (requires True)
  (ensures (fun s -> forall y . mem y s <==> x == y))

val union (#t: Type) (s1 s2: fset t) : Pure (fset t)
  (requires True)
  (ensures (fun s -> forall y . mem y s <==> (mem y s1 \/ mem y s2)))
