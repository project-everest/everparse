module CBOR.Spec.Raw.Set
open CBOR.Spec.Util

let order_total (#t: Type) (f: t -> t -> bool) : Tot prop =
  forall x y . x == y \/ f x y \/ f y x

let order (elt: Type) : Tot Type = (f: (elt -> elt -> bool) {
  order_irrefl f /\
  order_trans f /\
  order_total f
})

val t (#elt: eqtype) (f: order elt) : Tot eqtype

val cardinality (#elt: eqtype) (#f: order elt) (x: t f) : Tot nat

val mem (#elt: eqtype) (#f: order elt) (x: elt) (s: t f) : Tot bool

let equal (#elt: eqtype) (#f: order elt) (s1 s2: t f) : Tot prop =
  forall x . mem x s1 <==> mem x s2

val ext (#elt: eqtype) (#f: order elt) (s1 s2: t f) : Lemma
  (ensures (equal s1 s2 <==> s1 == s2))
  [SMTPat (equal s1 s2)]

val empty (#elt: eqtype) (f: order elt) : Tot (t f)

val mem_empty (#elt: eqtype) (f: order elt) (x: elt) : Lemma
  (ensures (~ (mem x (empty f))))
  [SMTPat (mem x (empty f))]

val cardinality_empty (#elt: eqtype) (f: order elt) : Lemma
  (ensures (cardinality (empty f) == 0))
  [SMTPat (cardinality (empty f))]

val singleton (#elt: eqtype) (f: order elt) (x: elt) : Tot (t f)

val mem_singleton (#elt: eqtype) (f: order elt) (x x': elt) : Lemma
  (ensures (mem x' (singleton f x) <==> x' == x))
  [SMTPat (mem x' (singleton f x))]

val cardinality_singleton (#elt: eqtype) (f: order elt) (x: elt) : Lemma
  (ensures (cardinality (singleton f x) == 1))
  [SMTPat (cardinality (singleton f x))]

val union (#elt: eqtype) (#f: order elt) (s1 s2: t f) : Tot (t f)

val mem_union (#elt: eqtype) (#f: order elt) (s1 s2: t f) (x: elt) : Lemma
  (ensures (mem x (union s1 s2) <==> (mem x s1 \/ mem x s2)))
  [SMTPat (mem x (union s1 s2))]

let disjoint (#elt: eqtype) (#f: order elt) (s1 s2: t f) : Tot prop =
  forall x . ~ (mem x s1 /\ mem x s2)

val cardinality_union (#elt: eqtype) (#f: order elt) (s1 s2: t f) : Lemma
  (requires (disjoint s1 s2))
  (ensures (cardinality (union s1 s2) == cardinality s1 + cardinality s2))
  [SMTPat (cardinality (union s1 s2))]

val filter (#elt: eqtype) (#f: order elt) (phi: elt -> bool) (s: t f) : Tot (t f)

val mem_filter (#elt: eqtype) (#f: order elt) (phi: elt -> bool) (s: t f) (x: elt) : Lemma
  (ensures (mem x (filter phi s) <==> (mem x s /\ phi x)))
  [SMTPat (mem x (filter phi s))]

val as_list (#elt: eqtype) (#f: order elt) (s: t f) : GTot (list elt)

val no_repeats_as_list (#elt: eqtype) (#f: order elt) (s: t f) : Lemma
  (ensures (List.Tot.no_repeats_p (as_list s)))
  [SMTPat (as_list s)]

val mem_as_list (#elt: eqtype) (#f: order elt) (s: t f) (x: elt) : Lemma
  (ensures (List.Tot.memP x (as_list s) <==> mem x s))
  [SMTPat (List.Tot.memP x (as_list s))]

val length_as_list (#elt: eqtype) (#f: order elt) (s: t f) : Lemma
  (ensures (List.Tot.length (as_list s) == cardinality s))
  [SMTPat (as_list s)]

val fold (#elt: eqtype) (#u: Type) (#f: order elt) (phi: u -> elt -> u) (x: u) (s: t f) : Tot u

val fold_ext
  (#elt: eqtype) (#u: Type) (#f: order elt) (phi1 phi2: u -> elt -> u) (x: u) (s: t f)
: Lemma
  (requires (forall x y . mem y s ==> phi1 x y == phi2 x y))
  (ensures (fold phi1 x s == fold phi2 x s))

val fold_eq
  (#elt: eqtype) (#u: Type) (#f: order elt) (phi: u -> elt -> u) (x: u) (s: t f) (l: list elt)
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
  (#elt: eqtype) (#u: Type) (#f: order elt) (phi: u -> elt -> u) (x: u) (s: t f) (l: list elt)
: Lemma
  (requires (
    op_comm phi /\
    op_idem phi /\
    (forall x . List.Tot.memP x l <==> mem x s)
  ))
  (ensures (
    fold phi x s == List.Tot.fold_left phi x l
  ))
