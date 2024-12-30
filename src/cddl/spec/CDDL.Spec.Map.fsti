module CDDL.Spec.Map
open CDDL.Spec.Base
module U = CBOR.Spec.Util
module S = CDDL.Spec.Set

val t
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  ([@@@strictly_positive] value: Type u#a)
: Tot (Type u#a)

val get
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
: t spec_key value -> key -> Tot (option value)

let defined
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
  (k: key) (f: t spec_key value)
: Tot bool
= Some? (get f k)

let equal
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
  (m1 m2: t spec_key value)
: Tot prop =
  (forall k . get m1 k == get m2 k)

val ext
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
  (m1 m2: t spec_key value)
: Lemma
  (ensures (equal m1 m2 <==> m1 == m2))
  [SMTPat (equal m1 m2)]

let mem
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
  (kv: (key & value))
  (f: t spec_key value)
: Tot prop
= get f (fst kv) == Some (snd kv)

let equal'
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
  (m1 m2: t spec_key value)
: Tot prop =
  (forall kv . mem kv m1 <==> mem kv m2)

let ext'
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
  (m1 m2: t spec_key value)
: Lemma
  (ensures (equal' m1 m2 <==> m1 == m2))
  [SMTPat (equal' m1 m2)]
= let prf
    (k: key)
  : Lemma
    (requires (equal' m1 m2))
    (ensures (get m1 k == get m2 k))
  = match get m1 k with
    | Some v -> assert (mem (k, v) m1)
    | _ ->
      begin match get m2 k with
      | Some v -> assert (mem (k, v) m2)
      | _ -> ()
      end
  in
  Classical.forall_intro (Classical.move_requires prf);
  assert (equal' m1 m2 ==> equal m1 m2)

val length
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
  (m: t spec_key value)
: Tot nat

val key_set
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
  (m: t spec_key value)
: Pure (S.t spec_key)
    (requires True)
    (ensures fun s ->
      S.cardinality s == length m /\
      (forall x . S.mem x s <==> defined x m)
    )

let defined_serializable
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type)
  (m: t spec_key value)
  (k: key)
: Lemma
  (ensures (defined k m ==> spec_key.serializable k))
  [SMTPat (get m k)]
= assert (defined k m ==> S.mem k (key_set m))

val empty
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  (value: Type u#a)
: t spec_key value

val get_empty
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  (value: Type u#a)
  (k: key)
: Lemma
  (ensures (get (empty spec_key value) k == None))
  [SMTPat (get (empty spec_key value) k)]

let length_empty
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  (value: Type u#a)
: Lemma
  (ensures (length (empty spec_key value) == 0))
  [SMTPat (length (empty spec_key value))]
= assert (S.equal (key_set (empty spec_key value)) (S.emptyset spec_key))

val singleton
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  (#value: Type u#a)
  (k: key { spec_key.serializable k })
  (v: value)
: t spec_key value

val get_singleton
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  (#value: Type u#a)
  (k: key { spec_key.serializable k })
  (v: value)
  (k': key)
: Lemma
  (ensures (
    let v' = get (singleton spec_key k v) k' in
    (k == k' ==> v' == Some v) /\
    ((~ (k == k')) ==> v' == None)
  ))
  [SMTPat (get (singleton spec_key k v) k')]

let length_singleton
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  (#value: Type u#a)
  (k: key { spec_key.serializable k })
  (v: value)
: Lemma
  (ensures (length (singleton spec_key k v) == 1))
  [SMTPat (length (singleton spec_key k v))]
= assert (S.equal (key_set (singleton spec_key k v)) (S.singleton spec_key k))

val union
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
: t spec_key value -> t spec_key value -> t spec_key value

val get_union
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
: (m1: t spec_key value) -> (m2: t spec_key value) -> (k: key) -> Lemma
  (ensures (get (union m1 m2) k == begin match get m1 k with
    | None -> get m2 k
    | v -> v
    end
  ))
  [SMTPat (get (union m1 m2) k)]

let disjoint
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (m1 m2: t spec_key value)
: Tot prop =
  forall k . ~ (defined k m1 /\ defined k m2)

let length_disjoint_union
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (m1 m2: t spec_key value)
: Lemma
  (requires (disjoint m1 m2))
  (ensures (
    length (union m1 m2) == length m1 + length m2
  ))
= assert (S.equal (key_set (union m1 m2)) (S.union (key_set m1) (key_set m2)));
  S.disjoint_union_cardinality (key_set m1) (key_set m2)

let union_assoc
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (m1 m2 m3: t spec_key value)
: Lemma
  (union (union m1 m2) m3 == union m1 (union m2 m3))
= ext
    (union (union m1 m2) m3)
    (union m1 (union m2 m3))

let union_empty_l
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (m: t spec_key value)
: Lemma
  (union (empty _ _) m == m)
  [SMTPat (union (empty _ _) m)]
= ext (union (empty _ _) m) m

let union_empty_r
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (m: t spec_key value)
: Lemma
  (union m (empty _ _) == m)
  [SMTPat (union m (empty _ _))]
= ext (union m (empty _ _)) m

let disjoint_union_comm
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (m1 m2: t spec_key value)
: Lemma
  (requires disjoint m1 m2)
  (ensures m1 `union` m2 == m2 `union` m1)
  [SMTPat (m1 `union` m2)]
= ext (m1 `union` m2) (m2 `union` m1)

val filter
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
:
  ((key & value) -> bool) ->
  t spec_key value ->
  t spec_key value

val get_filter
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
: (f: (key & value -> bool)) -> (m: t spec_key value) -> (k: key) -> Lemma
  (ensures (get (filter f m) k == begin match get m k with
  | None -> None
  | Some v -> if f (k, v) then Some v else None
  end))
  [SMTPat (get (filter f m) k)]

let filter_ext
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (f1 f2: (key & value) -> Tot bool)
  (m: t spec_key value)
: Lemma
  (requires forall x . f1 x == f2 x)
  (ensures filter f1 m == filter f2 m)
= ext (filter f1 m) (filter f2 m)

let disjoint_union_filter
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (f: (key & value) -> Tot bool)
  (m1 m2: t spec_key value)
: Lemma
  (requires disjoint m1 m2)
  (ensures (filter f (union m1 m2) == filter f m1 `union` filter f m2))
= ext
    (filter f (union m1 m2))
    (filter f m1 `union` filter f m2)

let filter_filter
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (p1 p2: (key & value) -> Tot bool)
  (f: t spec_key value)
: Lemma
  (filter p2 (filter p1 f) == filter (p1 `U.andp` p2) f)
= ext
    (filter p2 (filter p1 f))
    (filter (p1 `U.andp` p2) f)

let filter_implies
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (p1 p2: (key & value) -> Tot bool)
  (f: t spec_key value)
: Lemma
  (requires (forall kv . p1 kv ==> p2 kv))
  (ensures (filter p2 (filter p1 f) == filter p1 f))
= filter_filter p1 p2 f;
  filter_ext p1 (p1 `U.andp` p2) f

let for_all
  (#key: Type)
  (#key_s: typ)
  (#spec_key: spec key_s key true)
  (#value: Type u#a)
  (f: (key & value -> bool))
  (m: t spec_key value)
: Pure bool
    (requires True)
    (ensures fun b -> b <==> (forall kv . mem kv m ==> f kv))
= let b = (key_set (filter f m) = key_set m) in // HERE we use the fact that the key set is eqtype
  assert (b == true <==> equal (filter f m) m);
  b
