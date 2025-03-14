module CDDL.Spec.Set
module Cbor = CBOR.Spec.API.Type

let dummy_cbor : Cbor.cbor = Cbor.pack (Cbor.CSimple 0uy)

let set_prop
  (#target: Type) (#source: typ) (sp: spec source target true)
  (m: Cbor.cbor_map)
: Tot prop
= (forall (c: Cbor.cbor) . Cbor.cbor_map_defined c m ==> (source c /\ Cbor.cbor_map_get m c == Some dummy_cbor))

let t (#target: Type) (#source: typ) (sp: spec source target true) : Tot eqtype =
  (m: Cbor.cbor_map { set_prop sp m })

let mem (#target: Type) (#source: typ) (#sp: spec source target true)
  (x: target) (s: t sp)
: Tot bool
= sp.serializable x &&
  Cbor.cbor_map_defined (sp.serializer x) s

let mem_serializable (#target: Type) (#source: typ) (#sp: spec source target true)
  (x: target) (s: t sp)
: Lemma
  (ensures (mem x s ==> sp.serializable x))
  [SMTPat (mem x s)]
= ()

let rec list_target_of_list_cbor (#target: Type) (#source: typ) (sp: spec source target true)
  (l: list Cbor.cbor)
: Pure (list target)
    (requires (forall (x: Cbor.cbor) . List.Tot.memP x l ==> source x))
    (ensures (fun l' ->
      List.Tot.length l' == List.Tot.length l /\
      (forall (x': target) . List.Tot.memP x' l' <==> (sp.serializable x' /\ List.Tot.memP (sp.serializer x') l)) /\
      (List.Tot.no_repeats_p l ==> List.Tot.no_repeats_p l')
    ))
    (decreases l)
= match l with
  | [] -> []
  | a :: q -> sp.parser a :: list_target_of_list_cbor sp q

let cardinality
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s: t sp)
: Tot nat
= Cbor.cbor_map_length s

let set_as_list
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s: t sp)
: Ghost (list target)
    (requires True)
    (ensures (fun l ->
      List.Tot.length l == cardinality s /\
      List.Tot.no_repeats_p l /\
      (forall (x: target) . List.Tot.memP x l <==> mem x s)
    ))
= let l0 = Cbor.cbor_map_key_list s in
  list_target_of_list_cbor sp l0

let ext0
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s1 s2: t sp)
  (x: Cbor.cbor)
: Lemma
  (requires equal s1 s2)
  (ensures (Cbor.cbor_map_get s1 x == Cbor.cbor_map_get s2 x))
= match Cbor.cbor_map_get s1 x with
  | None ->
    begin match Cbor.cbor_map_get s2 x with
    | None -> ()
    | Some y ->
      assert (mem (sp.parser x) s2);
      assert (mem (sp.parser x) s1)
    end
  | Some y ->
    assert (mem (sp.parser x) s1);
    assert (mem (sp.parser x) s2)

let ext
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s1 s2: t sp)
: Lemma
  (equal s1 s2 <==> s1 == s2)
= Classical.forall_intro (Classical.move_requires (ext0 s1 s2));
  assert (equal s1 s2 <==> Cbor.cbor_map_equal s1 s2)

let fold_op
  (#target: Type) (#source: typ) (sp: spec source target true)
  (#a: Type)
  (f: a -> target -> a)
  (x: a)
  (y: Cbor.cbor)
: Tot a
= if source y
  then f x (sp.parser y)
  else x

let fold
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (#a: Type)
  (f: a -> target -> a)
  (x: a)
  (s: t sp)
: Tot a
= Cbor.cbor_map_fold (fold_op sp f) x s

let fold_ext
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
= Cbor.cbor_map_fold_ext (fold_op sp f1) (fold_op sp f2) x m m

let rec list_cbor_of_list_target (#target: Type) (#source: typ) (sp: spec source target true)
  (l: list target)
: Pure (list Cbor.cbor)
    (requires (forall (x: target) . List.Tot.memP x l ==> sp.serializable x))
    (ensures (fun l' ->
      List.Tot.length l' == List.Tot.length l /\
      (forall (x': Cbor.cbor) . List.Tot.memP x' l' <==> (source x' /\ List.Tot.memP (sp.parser x') l)) /\
      (List.Tot.no_repeats_p l ==> List.Tot.no_repeats_p l')
    ))
    (decreases l)
= match l with
  | [] -> []
  | a :: q -> sp.serializer a :: list_cbor_of_list_target sp q

let rec list_fold_list_cbor_of_list_target
  (#target: Type) (#source: typ) (sp: spec source target true)
  (#a: Type)
  (f: a -> target -> a)
  (x: a)
  (l: list target)
: Lemma
  (requires (forall (x: target) . List.Tot.memP x l ==> sp.serializable x))
  (ensures (
    List.Tot.fold_left (fold_op sp f) x (list_cbor_of_list_target sp l) == List.Tot.fold_left f x l
  ))
  (decreases l)
= match l with
  | [] -> ()
  | b :: q -> list_fold_list_cbor_of_list_target sp f (f x b) q

let fold_eq
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
= Cbor.cbor_map_fold_eq (fold_op sp f) x m (list_cbor_of_list_target sp l);
  list_fold_list_cbor_of_list_target sp f x l

let emptyset 
  (#target: Type) (#source: typ) (sp: spec source target true)
: Pure (t sp)
    (requires True)
    (ensures (fun s ->
      cardinality s == 0 /\
      (forall x . ~ (mem x s))
    ))
= Cbor.cbor_map_empty

let singleton
  (#target: Type) (#source: typ) (sp: spec source target true)
  (x: target)
: Pure (t sp)
    (requires sp.serializable x)
    (ensures fun s ->
      cardinality s == 1 /\
      (forall x' . mem x' s <==> x' == x)
    )
= Cbor.cbor_map_singleton (sp.serializer x) dummy_cbor

let union
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s1 s2: t sp)
: Pure (t sp)
    (requires True)
    (ensures fun s ->
      forall x' . mem x' s <==> (mem x' s1 \/ mem x' s2)
    )
= Cbor.cbor_map_union s1 s2

let disjoint_union_cardinality
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (s1 s2: t sp)
: Lemma
  (requires (disjoint s1 s2))
  (ensures (cardinality (union s1 s2) == cardinality s1 + cardinality s2))
= assert (forall (x: Cbor.cbor) . ~ (source x /\ mem (sp.parser x) s1 /\ mem (sp.parser x) s2));
  Cbor.cbor_map_length_disjoint_union s1 s2

let filter_op
  (#target: Type) (#source: typ) (sp: spec source target true)
  (f: target -> bool)
  (x: (Cbor.cbor & Cbor.cbor))
: Tot bool
= if source (fst x)
  then f (sp.parser (fst x))
  else false

let filter
  (#target: Type) (#source: typ) (#sp: spec source target true)
  (f: target -> bool)
  (s: t sp)
: Pure (t sp)
    (requires True)
    (ensures fun s' -> forall x . mem x s' <==> (mem x s /\ f x))
= Cbor.cbor_map_filter (filter_op sp f) s

let rec fold_inv'
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
  (s1: t sp)
  (l1: list target)
  (s2: t sp)
  (l2: list target)
: Lemma
  (requires (
    U.op_comm f /\
    (forall (x: target) . List.Tot.memP x l1 <==> mem x s1) /\
    (forall (x: target) . List.Tot.memP x l2 <==> mem x s2) /\
    List.Tot.no_repeats_p l1 /\
    List.Tot.no_repeats_p l2 /\
    disjoint s1 s2 /\
    inv s1 accu
  ))
  (ensures (
    inv (union s1 s2) (fold f accu s2)
  ))
  (decreases l2)
= fold_eq f accu s2 l2;
  match l2 with
  | [] -> assert (equal (union s1 s2) s1)
  | x :: l2' ->
    let s1' = union s1 (singleton sp x) in
    let l1' = x :: l1 in
    let s2' = filter (fun x' -> not (mem x' (singleton sp x))) s2 in
    let accu' = f accu x in
    succ accu x s1;
    fold_inv' inv f succ accu' s1' l1' s2' l2';
    assert (equal (union s1' s2') (union s1 s2));
    fold_eq f accu' s2' l2';
    ()

let fold_inv
  inv f succ accu s
= fold_inv' inv f succ accu (emptyset _) [] s (set_as_list s)
