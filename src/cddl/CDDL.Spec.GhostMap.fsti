module CDDL.Spec.GhostMap
module Cbor = CBOR.Spec

let notp_g
  (#t: Type)
  (p: (t -> GTot bool))
  (x: t)
: GTot bool
= not (p x)

let notp
  (#t: Type)
  (p: (t -> Tot bool))
  (x: t)
: Tot bool
= not (p x)

let rec list_length_filter
  (#t: Type)
  (f: t -> bool)
  (l: list t)
: Lemma
  (List.Tot.length (List.Tot.filter f l) <= List.Tot.length l)
  [SMTPat (List.Tot.length (List.Tot.filter f l))]
= match l with
  | [] -> ()
  | _ :: q -> list_length_filter f q

let rec list_memP_filter (#t: Type) (f: t -> bool) (l: list t) (x: t) : Lemma
  (ensures List.Tot.memP x (List.Tot.filter f l) <==> List.Tot.memP x l /\ f x)
  (decreases l)
  [SMTPat (List.Tot.memP x (List.Tot.filter f l))]
= match l with
  | [] -> ()
  | _ :: q -> list_memP_filter f q x

let list_memP_map
  (#a #b: Type)
  (f: a -> Tot b)
  (l: list a)
  (y: b)
: Lemma
  (ensures (List.Tot.memP y (List.Tot.map f l) <==> (exists (x : a) . List.Tot.memP x l /\ f x == y)))
= Classical.move_requires (List.Tot.memP_map_elim f y) l;
  Classical.forall_intro (fun x -> Classical.move_requires (List.Tot.memP_map_intro f x) l)

#restart-solver
let rec list_no_repeats_filter
  (#key #value: Type)
  (f: (key & value) -> bool)
  (l: list (key & value))
: Lemma
  (requires
    List.Tot.no_repeats_p (List.Tot.map fst l)
  )
  (ensures
    List.Tot.no_repeats_p (List.Tot.map fst (List.Tot.filter f l))
  )
  [SMTPat (List.Tot.no_repeats_p (List.Tot.map fst (List.Tot.filter f l)))]
= match l with
  | [] -> ()
  | (k, v) :: q ->
    list_no_repeats_filter f q;
    Classical.forall_intro (list_memP_map fst (List.Tot.filter f q));
    Classical.forall_intro (list_memP_map fst q)

[@@erasable]
val ghost_map (key value: Type0) : Type0

val apply_ghost_map (#key #value: Type0) (m: ghost_map key value) (k: key) : GTot (option value)

let ghost_map_feq (#key #value: Type) (m1 m2: ghost_map key value) : Tot prop
= forall x . apply_ghost_map m1 x == apply_ghost_map m2 x

val ghost_map_ext (#key #value: Type0) (m1 m2: ghost_map key value) : Lemma
  (requires ghost_map_feq m1 m2)
  (ensures m1 == m2)
  [SMTPat (ghost_map_feq m1 m2)]

let ghost_map_mem (#key #value: Type) (kv: (key & value)) (f: ghost_map key value) : Tot prop =
  apply_ghost_map f (fst kv) == Some (snd kv)

let ghost_map_equal (#key #value: Type) (f1 f2: ghost_map key value) : Tot prop
= forall kv . ghost_map_mem kv f1 <==> ghost_map_mem kv f2

val ghost_map_equiv (#key #value: Type) (f1 f2: ghost_map key value) : Lemma
  (requires ghost_map_equal f1 f2)
  (ensures f1 == f2)
  [SMTPat (ghost_map_equal f1 f2)]

let ghost_map_defined (#key #value: Type) (k: key) (f: ghost_map key value) : Tot prop =
  Some? (apply_ghost_map f k)

let ghost_map_defined_alt
  (#key #value: Type) (k: key) (f: ghost_map key value)
: Lemma
  (ghost_map_defined k f <==> (exists v . ghost_map_mem (k, v) f))
  [SMTPat (ghost_map_defined k f)]
= match apply_ghost_map f k with
  | None -> ()
  | Some _ -> ()

let ghost_map_disjoint (#key #value1 #value2: Type) (f1: ghost_map key value1) (f2: ghost_map key value2) : Tot prop =
  (forall k . ~ (ghost_map_defined k f1 /\ ghost_map_defined k f2))

val ghost_map_empty (#key #value: Type) : Tot (ghost_map key value)

val apply_ghost_map_empty (#key #value: Type) (k: key) : Lemma
  (apply_ghost_map (ghost_map_empty #key #value) k == None)
  [SMTPat (apply_ghost_map (ghost_map_empty #key #value) k)]

val ghost_map_singleton (#key #value: Type) (k: key) (v: value) : Tot (ghost_map key value)

val apply_ghost_map_singleton (#key #value: Type) (k: key) (v: value) (k': key) : Lemma
  (let res = apply_ghost_map (ghost_map_singleton k v) k' in
    (k == k' ==> res == Some v) /\ ((~ (k == k')) ==> res == None))
  [SMTPat (apply_ghost_map (ghost_map_singleton k v) k')]

val ghost_map_union (#key #value: Type) (m1 m2: ghost_map key value) : Tot (ghost_map key value)

val apply_ghost_map_union (#key #value: Type) (m1 m2: ghost_map key value) (k: key) : Lemma
  (apply_ghost_map (ghost_map_union m1 m2) k == begin match apply_ghost_map m1 k with
    | Some v -> Some v
    | None -> apply_ghost_map m2 k
  end)
  [SMTPat (apply_ghost_map (ghost_map_union m1 m2) k)]

let ghost_map_union_assoc (#key #value: Type) (m1 m2 m3: ghost_map key value) : Lemma
  (ghost_map_union (ghost_map_union m1 m2) m3 == ghost_map_union m1 (ghost_map_union m2 m3))
= ghost_map_ext
    (ghost_map_union (ghost_map_union m1 m2) m3)
    (ghost_map_union m1 (ghost_map_union m2 m3))

let ghost_map_union_empty_l (#key #value: Type) (m: ghost_map key value) : Lemma
  (ghost_map_union ghost_map_empty m == m)
  [SMTPat (ghost_map_union ghost_map_empty m)]
= ghost_map_ext (ghost_map_union ghost_map_empty m) m

let ghost_map_union_empty_r (#key #value: Type) (m: ghost_map key value) : Lemma
  (ghost_map_union m ghost_map_empty == m)
  [SMTPat (ghost_map_union m ghost_map_empty)]
= ghost_map_ext (ghost_map_union m ghost_map_empty) m

let ghost_map_disjoint_mem_union (#key #value: Type) (m1 m2: ghost_map key value) (xv: (key & value)) : Lemma
  (requires ghost_map_disjoint m1 m2)
  (ensures ghost_map_mem xv (m1 `ghost_map_union` m2) <==> ghost_map_mem xv m1 \/ ghost_map_mem xv m2)
= ()

let ghost_map_disjoint_mem_union' (#key #value: Type) (m1 m2: ghost_map key value) (_: squash (ghost_map_disjoint m1 m2)) : Lemma
  (ensures forall xv . ghost_map_mem xv (m1 `ghost_map_union` m2) <==> ghost_map_mem xv m1 \/ ghost_map_mem xv m2)
= ()

let ghost_map_disjoint_union_comm (#key #value: Type) (m1 m2: ghost_map key value) : Lemma
  (requires ghost_map_disjoint m1 m2)
  (ensures m1 `ghost_map_union` m2 == m2 `ghost_map_union` m1)
  [SMTPat (m1 `ghost_map_union` m2)]
= ghost_map_disjoint_mem_union' m1 m2 ();
  ghost_map_disjoint_mem_union' m2 m1 ();
  ghost_map_equiv (m1 `ghost_map_union` m2) (m2 `ghost_map_union` m1)

val ghost_map_length (#key #value: Type) (m: ghost_map key value) : GTot nat

val ghost_map_length_is_empty (#key #value: Type) (m: ghost_map key value)
: Lemma
  (ghost_map_length m == 0 <==> m == ghost_map_empty)

let ghost_map_length_empty (key value: Type) : Lemma
  (ghost_map_length (ghost_map_empty #key #value) == 0)
  [SMTPat (ghost_map_length (ghost_map_empty #key #value))]
= ghost_map_length_is_empty #key #value ghost_map_empty

val ghost_map_length_singleton (#key #value: Type) (k: key) (v: value) : Lemma
  (ghost_map_length (ghost_map_singleton k v) == 1)
  [SMTPat (ghost_map_length (ghost_map_singleton k v))]

val ghost_map_length_disjoint_union (#key #value: Type) (m1 m2: ghost_map key value) : Lemma
  (requires ghost_map_disjoint m1 m2)
  (ensures (ghost_map_length (ghost_map_union m1 m2) == ghost_map_length m1 + ghost_map_length m2))
  [SMTPat (ghost_map_length (ghost_map_union m1 m2))]


val ghost_map_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
: ghost_map key value

val apply_ghost_map_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
  (k: key)
: Lemma
  (apply_ghost_map (ghost_map_filter f m) k == begin match apply_ghost_map m k with
    | None -> None
    | Some v -> if f (k, v) then Some v else None
  end)
  [SMTPat (apply_ghost_map (ghost_map_filter f m) k)]

let ghost_map_mem_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
  (x: (key & value))
: Lemma
  (ghost_map_mem x (ghost_map_filter f m) <==> ghost_map_mem x m /\ f x)
= ()

let ghost_map_filter_for_all
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
: Lemma
  (requires forall x . ghost_map_mem x m ==> f x)
  (ensures ghost_map_filter f m == m)
= ghost_map_equiv (ghost_map_filter f m) m

let ghost_map_filter_for_all'
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
  (sq: squash (forall x . ghost_map_mem x m ==> f x))
: Lemma
  (ensures ghost_map_filter f m == m)
= ghost_map_filter_for_all f m

let ghost_map_filter_ext
  (#key #value: Type)
  (f1 f2: (key & value) -> GTot bool)
  (m: ghost_map key value)
: Lemma
  (requires forall x . f1 x == f2 x)
  (ensures ghost_map_filter f1 m == ghost_map_filter f2 m)
= ghost_map_equiv (ghost_map_filter f1 m) (ghost_map_filter f2 m)

let ghost_map_disjoint_union_filter
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m1 m2: ghost_map key value)
: Lemma
  (requires ghost_map_disjoint m1 m2)
  (ensures (ghost_map_filter f (ghost_map_union m1 m2) == ghost_map_filter f m1 `ghost_map_union` ghost_map_filter f m2))
= ghost_map_ext
    (ghost_map_filter f (ghost_map_union m1 m2))
    (ghost_map_filter f m1 `ghost_map_union` ghost_map_filter f m2)

let ghost_map_disjoint_union_filter'
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m1 m2: ghost_map key value)
  (sq: squash (ghost_map_disjoint m1 m2))
: Lemma
  (ensures (ghost_map_filter f (ghost_map_union m1 m2) == ghost_map_filter f m1 `ghost_map_union` ghost_map_filter f m2))
= ghost_map_disjoint_union_filter f m1 m2

val ghost_map_of_list
  (#key #value: Type)
  (l: list (key & value))
: ghost_map key value

val apply_ghost_map_of_list
  (#key #value: Type)
  (l: list (key & value))
  (k: key)
: Lemma
  (apply_ghost_map (ghost_map_of_list l) k == Cbor.list_ghost_assoc k l)
  [SMTPat (apply_ghost_map (ghost_map_of_list l) k)]

val ghost_map_of_list_singleton
  (#key #value: Type)
  (kv: (key & value))
: Lemma
  (ghost_map_of_list [kv] == ghost_map_singleton (fst kv) (snd kv))
  [SMTPat (ghost_map_of_list [kv])]

val ghost_map_of_list_append
  (#key #value: Type)
  (l1 l2: list (key & value))
: Lemma
  (ghost_map_of_list (List.Tot.append l1 l2) == ghost_map_of_list l1 `ghost_map_union` ghost_map_of_list l2)

val ghost_map_of_list_mem
  (#key #value: Type)
  (l: list (key & value) { List.Tot.no_repeats_p (List.Tot.map fst l) })
  (x: (key & value))
: Lemma
  (ghost_map_mem x (ghost_map_of_list l) <==> List.Tot.memP x l)
  [SMTPat (ghost_map_mem x (ghost_map_of_list l))]

val ghost_map_filter_of_list
  (#key #value: Type)
  (f: _ -> bool)
  (l: list (key & value) { List.Tot.no_repeats_p (List.Tot.map fst l) })
: Lemma
  (ghost_map_filter f (ghost_map_of_list l) == ghost_map_of_list (List.Tot.filter f l))
  [SMTPat (ghost_map_filter f (ghost_map_of_list l))]

val ghost_map_length_of_list
  (#key #value: Type)
  (l: list (key & value))
: Lemma
  (ensures ghost_map_length (ghost_map_of_list l) == List.Tot.length l <==> List.Tot.no_repeats_p (List.Tot.map fst l))
  [SMTPat (ghost_map_length (ghost_map_of_list l))]

let andp_g (#t: Type) (p1 p2: t -> GTot bool) (x: t) : GTot bool =
  p1 x && p2 x

let andp (#t: Type) (p1 p2: t -> Tot bool) (x: t) : Tot bool =
  p1 x && p2 x

let rec list_filter_filter (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (ensures (List.Tot.filter p2 (List.Tot.filter p1 l) == List.Tot.filter (andp p1 p2) l))
  (decreases l)
//  [SMTPat (List.Tot.filter p2 (List.Tot.filter p1 l))]
= match l with
  | [] -> ()
  | a :: q -> list_filter_filter p1 p2 q

let ghost_map_filter_filter
  (#key #value: Type)
  (p1 p2: (key & value) -> GTot bool)
  (f: ghost_map key value)
: Lemma
  (ghost_map_filter p2 (ghost_map_filter p1 f) == ghost_map_filter (p1 `andp_g` p2) f)
= ghost_map_equiv
    (ghost_map_filter p2 (ghost_map_filter p1 f))
    (ghost_map_filter (p1 `andp_g` p2) f)

let ghost_map_filter_implies
  (#key #value: Type)
  (p1 p2: (key & value) -> GTot bool)
  (f: ghost_map key value)
: Lemma
  (requires (forall kv . p1 kv ==> p2 kv))
  (ensures (ghost_map_filter p2 (ghost_map_filter p1 f) == ghost_map_filter p1 f))
= ghost_map_filter_filter p1 p2 f;
  ghost_map_filter_ext p1 (p1 `andp_g` p2) f

let rec list_filter_ext (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (requires forall (x: t) . List.Tot.memP x l ==> p1 x == p2 x)
  (ensures List.Tot.filter p1 l == List.Tot.filter p2 l)
  (decreases l)
= match l with
  | [] -> ()
  | a :: q -> list_filter_ext p1 p2 q

let list_filter_filter_comm (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (List.Tot.filter p2 (List.Tot.filter p1 l) == List.Tot.filter p1 (List.Tot.filter p2 l))
//  [SMTPat (List.Tot.filter p2 (List.Tot.filter p1 l))]
= list_filter_filter p1 p2 l;
  list_filter_filter p2 p1 l;
  list_filter_ext (andp p1 p2) (andp p2 p1) l

let list_filter_implies_1 (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (requires (forall (x: t) . (List.Tot.memP x l /\ p1 x) ==> p2 x))
  (ensures List.Tot.filter p2 (List.Tot.filter p1 l) == List.Tot.filter p1 l)
= list_filter_filter p1 p2 l;
  list_filter_ext p1 (andp p1 p2) l

let list_filter_implies_2 (#t: Type) (p1 p2: t -> bool) (l: list t) : Lemma
  (requires (forall (x: t) . (List.Tot.memP x l /\ p1 x) ==> p2 x))
  (ensures List.Tot.filter p1 (List.Tot.filter p2 l) == List.Tot.filter p1 l)
= list_filter_filter_comm p1 p2 l;
  list_filter_implies_1 p1 p2 l

let ghost_map_split
  (#key #value: Type)
  (f: (key & value) -> GTot bool)
  (m: ghost_map key value)
: Lemma (
    let mtrue = ghost_map_filter f m in
    let mfalse = ghost_map_filter (notp_g f) m in
    mtrue `ghost_map_disjoint` mfalse /\
    mtrue `ghost_map_union` mfalse == m
  )
= let mtrue = ghost_map_filter f m in
  let mfalse = ghost_map_filter (notp_g f) m in
  assert (mtrue `ghost_map_disjoint` mfalse);
  ghost_map_ext (mtrue `ghost_map_union` mfalse) m

#restart-solver
let ghost_map_disjoint_union_simpl_l
  (#key #value: Type)
  (g g1 g2: ghost_map key value)
: Lemma
  (requires
    g `ghost_map_disjoint` g1 /\
    g `ghost_map_disjoint` g2 /\
    g `ghost_map_union` g1 == g `ghost_map_union` g2
  )
  (ensures g1 == g2)
= assert (forall x . ghost_map_mem x g1 <==> (ghost_map_mem x (g `ghost_map_union` g1) /\ ~ (ghost_map_mem x g)));
  ghost_map_equiv g1 g2

#restart-solver
let ghost_map_disjoint_union_simpl_r
  (#key #value: Type)
  (g1 g2 g: ghost_map key value)
: Lemma
  (requires
    g1 `ghost_map_disjoint` g /\
    g2 `ghost_map_disjoint` g /\
    g1 `ghost_map_union` g == g2 `ghost_map_union` g
  )
  (ensures g1 == g2)
= ghost_map_disjoint_union_comm g1 g;
  ghost_map_disjoint_union_comm g2 g;
  ghost_map_disjoint_union_simpl_l g g1 g2

let ghost_map_included
  (#key #value: Type)
  (m1 m2: ghost_map key value)
: Tot prop
= forall x . ghost_map_mem x m1 ==> ghost_map_mem x m2

val ghost_map_sub
  (#key #value: Type)
  (m1 m2: ghost_map key value)
: Pure (ghost_map key value)
    (requires ghost_map_included m2 m1)
    (ensures fun m3 ->
      m2 `ghost_map_disjoint` m3 /\
      m2 `ghost_map_union` m3 == m1
    )
