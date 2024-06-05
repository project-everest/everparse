module CBOR.Spec.FiniteMap

let eq_elem_test_codom (#t: Type) (x: t) (y: t) : Type =
  (z: bool { z == true <==> x == y })

let eq_elem_test (#t: Type) (x: t) : Type =
  (y: t) -> (eq_elem_test_codom x y)

let eq_test (t: Type) =
  (x: t) -> eq_elem_test x

val fmap (t: Type u#a) (u: Type u#b) : Type u#(max a b)

val fmap_eq (#t #u: Type) : eq_test (fmap t u)

val get (#t #u: Type) (x: t) (s: fmap t u) : Tot (option u)

let equal
  (#t #u: Type)
  (s1 s2: fmap t u)
: Tot prop
= forall x . get x s1 == get x s2

val equal_eq
  (#t #u: Type)
  (s1 s2: fmap t u)
: Lemma
  (equal s1 s2 <==> s1 == s2)
  [SMTPat (equal s1 s2)]

val empty (t u: Type) : Pure (fmap t u)
  (requires True)
  (ensures (fun s -> forall x . None? (get x s)))

val singleton (#t #u: Type) (x: t) (elt: u) (eq: eq_elem_test x) (equ: eq_elem_test elt) : Pure (fmap t u)
  (requires True)
  (ensures (fun s -> get x s == Some elt /\ (forall y . (~ (x == y)) ==>  get y s == None)))

val union (#t #u: Type) (s1 s2: fmap t u) : Pure (fmap t u)
  (requires True)
  (ensures (fun s -> forall y . get y s == begin match get y s1 with
  | Some v -> Some v
  | _ -> get y s2
  end))
