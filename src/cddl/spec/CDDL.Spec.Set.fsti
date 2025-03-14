module CDDL.Spec.Set
open CDDL.Spec.Base
module U = CBOR.Spec.Util

val t (#target: Type) (#source: typ) (sp: spec source target true) : Tot eqtype

val mem (#target: Type) (#source: typ) (#sp: spec source target true)
  (x: target) (s: t sp)
: Tot bool

val mem_serializable (#target: Type) (#source: typ) (#sp: spec source target true)
  (x: target) (s: t sp)
: Lemma
  (ensures (mem x s ==> sp.serializable x))
  [SMTPat (mem x s)]

val cardinality
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s: t sp)
: Tot nat

val set_as_list
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s: t sp)
: Ghost (list target)
    (requires True)
    (ensures (fun l ->
      List.Tot.length l == cardinality s /\
      List.Tot.no_repeats_p l /\
      (forall (x: target) . List.Tot.memP x l <==> mem x s)
    ))

let equal
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s1 s2: t sp)
: Tot prop
= (forall x . mem x s1 <==> mem x s2)

val ext
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s1 s2: t sp)
: Lemma
  (ensures (equal s1 s2 <==> s1 == s2))
  [SMTPat (equal s1 s2)]

val fold
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (#a: Type)
  (f: a -> target -> a)
  (x: a)
  (s: t sp)
: Tot a

val fold_ext
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (#a: Type)
  (f1 f2: a -> target -> a)
  (x: a)
  (m: t sp)
: Lemma
  (requires (
    (forall (x: a) (y: target) . mem y m ==> f1 x y == f2 x y)
  ))
  (ensures (fold f1 x m == fold f2 x m))

val fold_eq
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (#a: Type)
  (f: a -> target -> a)
  (x: a)
  (m: t sp)
  (l: list target)
: Lemma
  (requires (
    U.op_comm f /\
    (forall (x: target) . List.Tot.memP x l <==> mem x m) /\
    List.Tot.no_repeats_p l
  ))
  (ensures (
    fold f x m == List.Tot.fold_left f x l
  ))

val emptyset 
  (#target: Type) (#source: typ) (sp: spec source target true)
: Pure (t sp)
    (requires True)
    (ensures (fun s ->
      cardinality s == 0 /\
      (forall x . ~ (mem x s))
    ))

val singleton
  (#target: Type) (#source: typ) (sp: spec source target true)
  (x: target)
: Pure (t sp)
    (requires sp.serializable x)
    (ensures fun s ->
      cardinality s == 1 /\
      (forall x' . mem x' s <==> x' == x)
    )

val union
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s1 s2: t sp)
: Pure (t sp)
    (requires True)
    (ensures fun s ->
      forall x' . mem x' s <==> (mem x' s1 \/ mem x' s2)
    )

let disjoint
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s1 s2: t sp)
: Tot prop
= forall x . ~ (mem x s1 /\ mem x s2)

val disjoint_union_cardinality
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s1 s2: t sp)
: Lemma
  (requires (disjoint s1 s2))
  (ensures (cardinality (union s1 s2) == cardinality s1 + cardinality s2))

val filter
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (f: target -> bool)
  (s: t sp)
: Pure (t sp)
    (requires True)
    (ensures fun s' -> forall x . mem x s' <==> (mem x s /\ f x))

val fold_inv
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (#a: Type)
  (inv: (t sp -> a -> prop))
  (f: a -> target -> a)
  (succ: (
    (accu: a) ->
    (k: target) ->
    (s: t sp) ->
    Lemma
    (requires (inv s accu /\ sp.serializable k))
    (ensures (inv (union s (singleton sp k)) (f accu k)))
  ))
  (accu: a)
  (s: t sp)
: Lemma
  (requires (
    U.op_comm f /\
    inv (emptyset sp) accu
  ))
  (ensures (inv s (fold f accu s)))
