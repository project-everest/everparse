module CBOR.Spec.API.MapPairSet
open CBOR.Spec.API.Type
open CBOR.Spec.Util

let elt = cbor_map & cbor_map

val t : eqtype

val cardinality (x: t) : Tot nat

val mem (x: elt) (s: t) : Tot bool

let equal (s1 s2: t) : Tot prop =
  forall x . mem x s1 <==> mem x s2

val ext (s1 s2: t) : Lemma
  (ensures (equal s1 s2 <==> s1 == s2))
  [SMTPat (equal s1 s2)]

val empty : t

val mem_empty (x: elt) : Lemma
  (ensures (~ (mem x (empty))))
  [SMTPat (mem x (empty))]

val cardinality_empty : squash
  (cardinality (empty) == 0)

val singleton (x: elt) : Tot (t)

val mem_singleton (x x': elt) : Lemma
  (ensures (mem x' (singleton x) <==> x' == x))
  [SMTPat (mem x' (singleton x))]

val cardinality_singleton (x: elt) : Lemma
  (ensures (cardinality (singleton x) == 1))
  [SMTPat (cardinality (singleton x))]

val union (s1 s2: t) : Tot (t)

val mem_union (s1 s2: t) (x: elt) : Lemma
  (ensures (mem x (union s1 s2) <==> (mem x s1 \/ mem x s2)))
  [SMTPat (mem x (union s1 s2))]

let disjoint (s1 s2: t) : Tot prop =
  forall x . ~ (mem x s1 /\ mem x s2)

val cardinality_union (s1 s2: t) : Lemma
  (requires (disjoint s1 s2))
  (ensures (cardinality (union s1 s2) == cardinality s1 + cardinality s2))
  [SMTPat (cardinality (union s1 s2))]

val filter (phi: elt -> bool) (s: t) : Tot (t)

val mem_filter (phi: elt -> bool) (s: t) (x: elt) : Lemma
  (ensures (mem x (filter phi s) <==> (mem x s /\ phi x)))
  [SMTPat (mem x (filter phi s))]

val as_list (s: t) : GTot (list elt)

val no_repeats_as_list (s: t) : Lemma
  (ensures (List.Tot.no_repeats_p (as_list s)))
  [SMTPat (as_list s)]

val mem_as_list (s: t) (x: elt) : Lemma
  (ensures (List.Tot.memP x (as_list s) <==> mem x s))
  [SMTPatOr [
    [SMTPat (List.Tot.memP x (as_list s))];
    [SMTPat (mem x s)];
  ]]

val length_as_list (s: t) : Lemma
  (ensures (List.Tot.length (as_list s) == cardinality s))
  [SMTPatOr [
    [SMTPat (as_list s)];
    [SMTPat (cardinality s)];
  ]]

val fold (#u: Type) (phi: u -> elt -> u) (x: u) (s: t) : Tot u

val fold_ext
  (#u: Type) (phi1 phi2: u -> elt -> u) (x: u) (s: t)
: Lemma
  (requires (forall x y . mem y s ==> phi1 x y == phi2 x y))
  (ensures (fold phi1 x s == fold phi2 x s))

val fold_eq
  (#u: Type) (phi: u -> elt -> u) (x: u) (s: t) (l: list elt)
: Lemma
  (requires (
    op_comm phi /\
    List.Tot.no_repeats_p l /\
    (forall x . List.Tot.memP x l <==> mem x s)
  ))
  (ensures (
    fold phi x s == List.Tot.fold_left phi x l
  ))

val fold_eq_idem
  (#u: Type) (phi: u -> elt -> u) (x: u) (s: t) (l: list elt)
: Lemma
  (requires (
    op_comm phi /\
    op_idem phi /\
    (forall x . List.Tot.memP x l <==> mem x s)
  ))
  (ensures (
    fold phi x s == List.Tot.fold_left phi x l
  ))

let singleton_elim
  (s: t)
: Pure elt
    (requires cardinality s == 1)
    (ensures fun x -> equal s (singleton x))
= let l = Ghost.hide (as_list s) in
  assert (forall x . List.Tot.memP x l <==> mem x s);
  assert (List.Tot.length l == 1);
  assert (forall x . mem x s <==> x == List.Tot.hd l);
  let t = (x: elt { mem x s }) in
  let f (accu: option t) (x: elt) : Tot (option t) =
    if mem x s
    then Some x
    else accu
  in
  fold_eq f None s l;
  let ores : option t = fold f None s in
  assert (Some? ores);
  Some?.v ores
