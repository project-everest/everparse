module CDDL.Spec.Map
open CDDL.Spec.Base
module U = CBOR.Spec.Util
module S = CDDL.Spec.Set

val t
  (key: Type0)
  ([@@@strictly_positive] value: Type u#a)
: Tot (Type u#a)

val get
  (#key: Type)
  (#value: Type)
: t key value -> key -> Tot (option value)

let defined
  (#key: Type)
  (#value: Type)
  (k: key) (f: t key value)
: Tot bool
= Some? (get f k)

let equal
  (#key: Type)
  (#value: Type)
  (m1 m2: t key value)
: Tot prop =
  (forall k . get m1 k == get m2 k)

val ext
  (#key: Type)
  (#value: Type)
  (m1 m2: t key value)
: Lemma
  (ensures (equal m1 m2 <==> m1 == m2))
  [SMTPat (equal m1 m2)]

let mem
  (#key: Type)
  (#value: Type)
  (kv: (key & value))
  (f: t key value)
: Tot prop
= get f (fst kv) == Some (snd kv)

let mem_defined
  (#key: Type)
  (#value: Type)
  (k: key)
  (f: t key value)
: Lemma
  (match get f k with
  | None -> True
  | Some v -> mem (k, v) f
  )
  [SMTPat (get f k)]
= ()

let equal'
  (#key: Type)
  (#value: Type)
  (m1 m2: t key value)
: Tot prop =
  (forall kv . mem kv m1 <==> mem kv m2)

let ext'
  (#key: Type)
  (#value: Type)
  (m1 m2: t key value)
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
  (#value: Type)
  (m: t key value)
: Tot nat

val key_set
  (#key: Type)
  (#key_s: typ)
  (spec_key: spec key_s key true)
  (#value: Type)
  (m: t key value)
: Pure (S.t spec_key)
    (requires (
      forall (x: key) . defined x m ==> spec_key.serializable x
    ))
    (ensures fun s ->
      S.cardinality s == length m /\
      (forall x . S.mem x s <==> defined x m)
    )

val empty
  (key: Type)
  (value: Type u#a)
: t key value

val get_empty
  (#key: Type)
  (value: Type u#a)
  (k: key)
: Lemma
  (ensures (get (empty key value) k == None))
  [SMTPat (get (empty key value) k)]

val length_empty
  (key: Type)
  (value: Type u#a)
: Lemma
  (ensures (length (empty key value) == 0))
  [SMTPat (length (empty key value))]

val singleton
  (#key: Type)
  (#value: Type u#a)
  (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: value)
: t key value

val get_singleton
  (#key: Type)
  (#value: Type u#a)
  (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: value)
  (k': key)
: Lemma
  (ensures (
    let v' = get (singleton k k_eq v) k' in
    (k == k' ==> v' == Some v) /\
    ((~ (k == k')) ==> v' == None)
  ))
  [SMTPat (get (singleton k k_eq v) k')]

val length_singleton
  (#key: Type)
  (#value: Type u#a)
  (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: value)
: Lemma
  (ensures (length (singleton k k_eq v) == 1))
  [SMTPat (length (singleton k k_eq v))]

val union
  (#key: Type)
  (#value: Type u#a)
: t key value -> t key value -> t key value

val get_union
  (#key: Type)
  (#value: Type u#a)
: (m1: t key value) -> (m2: t key value) -> (k: key) -> Lemma
  (ensures (get (union m1 m2) k == begin match get m1 k with
    | None -> get m2 k
    | v -> v
    end
  ))
  [SMTPat (get (union m1 m2) k)]

let disjoint
  (#key: Type)
  (#value: Type u#a)
  (m1 m2: t key value)
: Tot prop =
  forall k . ~ (defined k m1 /\ defined k m2)

val length_disjoint_union
  (#key: Type)
  (#value: Type u#a)
  (m1 m2: t key value)
: Lemma
  (requires (disjoint m1 m2))
  (ensures (
    length (union m1 m2) == length m1 + length m2
  ))

let union_assoc
  (#key: Type)
  (#value: Type u#a)
  (m1 m2 m3: t key value)
: Lemma
  (union (union m1 m2) m3 == union m1 (union m2 m3))
= ext
    (union (union m1 m2) m3)
    (union m1 (union m2 m3))

let union_empty_l
  (#key: Type)
  (#value: Type u#a)
  (m: t key value)
: Lemma
  (union (empty _ _) m == m)
  [SMTPat (union (empty _ _) m)]
= ext (union (empty _ _) m) m

let union_empty_r
  (#key: Type)
  (#value: Type u#a)
  (m: t key value)
: Lemma
  (union m (empty _ _) == m)
  [SMTPat (union m (empty _ _))]
= ext (union m (empty _ _)) m

let disjoint_union_comm
  (#key: Type)
  (#value: Type u#a)
  (m1 m2: t key value)
: Lemma
  (requires disjoint m1 m2)
  (ensures m1 `union` m2 == m2 `union` m1)
  [SMTPat (m1 `union` m2)]
= ext (m1 `union` m2) (m2 `union` m1)

val filter
  (#key: Type)
  (#value: Type u#a)
:
  ((key & value) -> bool) ->
  t key value ->
  t key value

val get_filter
  (#key: Type)
  (#value: Type u#a)
: (f: (key & value -> bool)) -> (m: t key value) -> (k: key) -> Lemma
  (ensures (get (filter f m) k == begin match get m k with
  | None -> None
  | Some v -> if f (k, v) then Some v else None
  end))
  [SMTPat (get (filter f m) k)]

let filter_ext
  (#key: Type)
  (#value: Type u#a)
  (f1 f2: (key & value) -> Tot bool)
  (m: t key value)
: Lemma
  (requires forall x . f1 x == f2 x)
  (ensures filter f1 m == filter f2 m)
= ext (filter f1 m) (filter f2 m)

let disjoint_union_filter
  (#key: Type)
  (#value: Type u#a)
  (f: (key & value) -> Tot bool)
  (m1 m2: t key value)
: Lemma
  (requires disjoint m1 m2)
  (ensures (filter f (union m1 m2) == filter f m1 `union` filter f m2))
= ext
    (filter f (union m1 m2))
    (filter f m1 `union` filter f m2)

let filter_filter
  (#key: Type)
  (#value: Type u#a)
  (p1 p2: (key & value) -> Tot bool)
  (f: t key value)
: Lemma
  (filter p2 (filter p1 f) == filter (p1 `U.andp` p2) f)
= ext
    (filter p2 (filter p1 f))
    (filter (p1 `U.andp` p2) f)

let filter_implies
  (#key: Type)
  (#value: Type u#a)
  (p1 p2: (key & value) -> Tot bool)
  (f: t key value)
: Lemma
  (requires (forall kv . p1 kv ==> p2 kv))
  (ensures (filter p2 (filter p1 f) == filter p1 f))
= filter_filter p1 p2 f;
  filter_ext p1 (p1 `U.andp` p2) f

let set
  (#key: Type)
  (#value: Type)
  (m: t key value)
  (k: key)
  (k_eq: ((k' : key) -> Pure bool True (fun res -> res == true <==> k'  == k)))
  (v: value)
: Pure (t key value)
    True
    (fun m' ->
      forall k' . {:pattern get m' k'} get m' k' == (if k_eq k' then Some v else get m k')
    )
= union (singleton k k_eq v) (filter (fun (k', _) -> not (k_eq k')) m)

val for_all
  (#key: Type)
  (#value: Type u#a)
  (f: (key & value -> bool))
  (m: t key value)
: Pure bool
    (requires True)
    (ensures fun b -> b <==> (forall kv . mem kv m ==> f kv))

let for_all_keys
  (#key: Type)
  (#value: Type u#a)
  (f: (key -> bool))
  (m: t key value)
: Pure bool
    (requires True)
    (ensures fun b -> b <==> (forall k . defined k m ==> f k))
= for_all (fun kv -> f (fst kv)) m

let included
  (#key: Type)
  (#value: Type u#a)
  (f: (x: value) -> (y: value) -> Pure bool (requires True) (ensures fun z -> z == true <==> x == y))
  (m1 m2: t key value)
: Pure bool
    (requires True)
    (ensures fun b -> b == true <==> (forall k . defined k m1 ==> get m1 k == get m2 k))
= for_all (fun (k, v) -> match get m2 k with None -> false | Some v' -> f v v') m1

let equal_bool
  (#key: Type)
  (#value: Type u#a)
  (f: (x: value) -> (y: value) -> Pure bool (requires True) (ensures fun z -> z == true <==> x == y))
  (m1 m2: t key value)
: Pure bool
    (requires True)
    (ensures fun b -> b == true ==> m1 == m2)
= let res = included f m1 m2 && included f m2 m1 in
  assert (res == true <==> equal m1 m2);
  res
