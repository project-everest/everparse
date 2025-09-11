module CDDL.Spec.Map
module F = FStar.FunctionalExtensionality
module Util = CBOR.Spec.Util

let ( ^-> ) = F.op_Hat_Subtraction_Greater

noeq
type uunit : Type u#a = | UU

let codom
  (#key: Type0)
  (dom: (key -> bool))
  ([@@@strictly_positive] value: Type u#a)
  (k: key)
: Tot (Type u#a)
= if dom k then value else uunit

let fold_op
  (key: Type)
  (accu: Type)
= (f: (accu -> key -> accu) { Util.op_comm f })

let is_enum_of
  (#key: Type)
  (dom: (key -> bool))
  (l: list key)
: Tot prop
= List.Tot.no_repeats_p l /\
  (forall k . List.Tot.memP k l <==> dom k == true)

let enum_of
  (#key: Type)
  (dom: (key -> bool))
= (l: list key { is_enum_of dom l })

let fold_t
  (key: Type)
  (accu: Type)
= fold_op key accu ^-> (accu ^-> accu)

let is_fold_of
  (#key: Type)
  (dom: (key -> bool))
  (#accu: Type)
  (f: fold_t key accu)
: Tot prop
= forall (op: fold_op key accu) (l: enum_of dom) (x: accu) . f op x == List.Tot.fold_left op x l

let fold_of
  (#key: Type)
  (dom: (key -> bool))
  (accu: Type)
= (f: fold_t key accu { is_fold_of dom f })

let fold_of_intro
  (#key: Type)
  (dom: (key -> bool))
  (l: Ghost.erased (enum_of dom))
  (accu: Type)
  (f: (fold_op key accu -> accu -> accu))
: Pure (fold_of dom accu)
    (requires (forall (op: fold_op key accu) (x: accu) . f op x == List.Tot.fold_left op x l))
    (ensures (fun _ -> True))
= let res : fold_t key accu =
    F.on_dom (fold_op key accu) (fun op ->
      F.on_dom accu (fun x ->
        f op x
      )
    )
  in
  let prf
    (op: fold_op key accu)
    (l': enum_of dom)
    (x: accu)
  : Lemma
    (res op x == List.Tot.fold_left op x l')
  = Util.list_fold_ext_no_repeats_p op x l l'
  in
  Classical.forall_intro_3 prf;
  res

let fold_of_elim
  (#key: Type)
  (dom: (key -> bool))
  (#accu: Type)
  (f: fold_of dom accu)
  (op: fold_op key accu)
  (l: enum_of dom)
  (x: accu)
: Lemma
  (f op x == List.Tot.fold_left op x l)
= ()

let nondep_feq
  (#a #b: Type)
  (f1 f2: (a -> b))
: Tot prop
= F.feq f1 f2

let nondep_feq_elim
  (#a #b: Type)
  (f1 f2: (a ^-> b))
: Lemma
  (requires (nondep_feq f1 f2))
  (ensures (f1 == f2))
= ()

let fold_of_unique
  (#key: Type)
  (dom: (key -> bool))
  (dom_ex: squash (enum_of dom))
  (#accu: Type)
  (f1 f2: fold_of dom accu)
: Lemma
  (ensures (f1 == f2))
= let l : enum_of dom = FStar.IndefiniteDescription.elim_squash dom_ex in
  assert (forall (op: fold_op key accu) x . f1 op x == List.Tot.fold_left op x l);
  assert (forall (op: fold_op key accu) x . f2 op x == List.Tot.fold_left op x l);
  let prf
    (op: fold_op key accu)
  : Lemma
    (f1 op == f2 op)
  = assert (forall x . f1 op x == List.Tot.fold_left op x l);
    assert (forall x . f2 op x == List.Tot.fold_left op x l);
    assert (F.feq (f1 op) (f2 op));
    nondep_feq_elim (f1 op) (f2 op)
  in
  Classical.forall_intro prf;
  assert (F.feq f1 f2);
  nondep_feq_elim f1 f2

noeq
type key_set_dom
  (#key: Type)
  (dom: (key -> bool))
= {
  dom_key_s: typ;
  dom_key_spec: spec dom_key_s key true;
  dom_key_filter: (key -> bool);
  dom_key_prop: squash (forall (x: key) . (dom x && dom_key_filter x) ==> dom_key_spec.serializable x);
}

let key_set_codom
  (#key: Type)
  (dom: (key -> bool))
  (sdom: key_set_dom dom)
= (s: S.t sdom.dom_key_spec { forall x . S.mem x s <==> (dom x && sdom.dom_key_filter x) })

noeq
type t
  (key: Type0)
  (value: Type u#a)
: Type u#a
= {
  dom: key ^-> bool;
  dom_ex: squash (enum_of dom);
  dom_fold_bool: fold_of dom bool;
  dom_fold_nat: fold_of dom nat;
  dom_key_set: F.restricted_t (key_set_dom dom) (key_set_codom dom);
  map: F.restricted_t key (codom dom value);
}

let get m k =
  if m.dom k
  then Some (m.map k)
  else None

let ext #key #value m1 m2 =
  let prf
    ()
  : Lemma
    (requires (equal m1 m2))
    (ensures (m1 == m2))
  = assert (F.feq m1.dom m2.dom);
    nondep_feq_elim m1.dom m2.dom;
    assert (m1.dom == m2.dom);
    assert (forall (d: key_set_dom m1.dom) . S.equal (m1.dom_key_set d) (m2.dom_key_set d));
    assert (F.feq m1.dom_key_set m2.dom_key_set);
    fold_of_unique m1.dom m1.dom_ex m1.dom_fold_bool m2.dom_fold_bool;
    fold_of_unique m1.dom m1.dom_ex m1.dom_fold_nat m2.dom_fold_nat;
    assert (F.feq m1.map m2.map)
  in
  Classical.move_requires prf ()

let length m = m.dom_fold_nat (Util.list_length_as_fold_op _) 0

let key_set #key #key_s spec_key #value m =
  let d : key_set_dom m.dom = {
    dom_key_s = key_s;
    dom_key_spec = spec_key;
    dom_key_filter = (fun _ -> true);
    dom_key_prop = ();
  } in
  let res = m.dom_key_set d in
  let l = Ghost.hide (FStar.IndefiniteDescription.elim_squash m.dom_ex) in
  let l' = Ghost.hide (S.set_as_list res) in
  Util.list_length_as_fold l 0;
  Util.list_length_as_fold l' 0;
  Util.list_fold_ext_no_repeats_p (Util.list_length_as_fold_op _) 0 l l';
  res

let fold_of_intro_empty
  (#key: Type)
  (dom: key -> bool)
  (accu: Type)
: Pure (fold_of dom accu)
    (requires (forall x . dom x == false))
    (ensures (fun _ -> True))
= let l : enum_of dom = [] in
  fold_of_intro dom l accu (fun _ x -> x)

let empty key value =
  let dom = F.on_dom key (fun _ -> false) in
  let l : enum_of dom = [] in
  {
    dom = dom;
    dom_ex = ();
    dom_fold_bool = fold_of_intro_empty dom bool;
    dom_fold_nat = fold_of_intro_empty dom nat;
    dom_key_set = F.on_dom (key_set_dom dom) #(key_set_codom dom) (fun d -> S.emptyset _);
    map = F.on_dom key #(codom dom value) (fun _ -> UU);
  }

let get_empty #key value k = ()

let length_empty key value = ()

let fold_of_intro_singleton
  (#key: Type)
  (dom: key -> bool)
  (elt: key)
  (accu: Type)
: Pure (fold_of dom accu)
    (requires (forall x . dom x == true <==> x == elt))
    (ensures (fun _ -> True))
= let l : enum_of dom = [elt] in
  fold_of_intro dom l accu (fun op x -> op x elt)

let singleton #key #value k k_eq v =
  let dom = F.on_dom key (fun k' -> k_eq k') in
  let l : enum_of dom = [k] in
  {
    dom = dom;
    dom_ex = ();
    dom_fold_bool = fold_of_intro_singleton dom k bool;
    dom_fold_nat = fold_of_intro_singleton dom k nat;
    dom_key_set = F.on_dom (key_set_dom dom) #(key_set_codom dom) (fun d -> if d.dom_key_filter k then S.singleton _ k else S.emptyset _);
    map = F.on_dom key #(codom dom value) (fun k' -> if k_eq k' then v else UU);
  }

let get_singleton k k_eq v k' = ()

let length_singleton k k_eq v = ()

let fold_of_intro_filter
  (#key: Type)
  (dom: key -> bool)
  (dom0: key -> bool)
  (l0: Ghost.erased (enum_of dom0))
  (phi: key -> bool)
  (accu: Type)
  (f0: fold_of dom0 accu)
: Pure (fold_of dom accu)
    (requires forall k . dom k == true <==> (dom0 k == true /\ phi k == true))
    (ensures fun _ -> True)
= let l : Ghost.erased (enum_of dom) = List.Tot.filter phi l0 in
  Classical.forall_intro_2 (Util.list_fold_filter #_ #accu phi l0);
  fold_of_intro dom l accu (fun op x -> f0 (Util.list_fold_filter_op phi op) x)

let fold_of_intro_union
  (#key: Type)
  (dom dom1 dom2: key -> bool)
  (l1: Ghost.erased (enum_of dom1))
  (l2: Ghost.erased (enum_of dom2))
  (accu: Type)
  (f1: fold_of dom1 accu)
  (f2: fold_of dom2 accu)
: Pure (fold_of dom accu)
    (requires forall k . dom k == true <==> (dom1 k == true \/ dom2 k == true))
    (ensures fun _ -> True)
= Util.union_as_list l1 l2 dom2;
  let l : Ghost.erased (enum_of dom) = List.Tot.append (List.Tot.filter (Util.notp dom2) l1) l2 in
  let dom1' (k: key) : Tot bool =
    dom1 k && not (dom2 k)
  in
  let f (op: fold_op key accu) (x: accu) : Tot accu =
    let x1 = fold_of_intro_filter dom1' dom1 l1 (Util.notp dom2) accu f1 op x in
    f2 op x1
  in
  let prf
    (op: fold_op key accu)
    (x: accu)
  : Lemma
    (f op x == List.Tot.fold_left op x l)
  =
    List.Tot.fold_left_append op (List.Tot.filter (Util.notp dom2) l1) l2
  in
  Classical.forall_intro_2 prf;
  fold_of_intro dom l accu f

let union #key #value m1 m2 =
  let dom = F.on_dom key (fun k -> m1.dom k || m2.dom k) in
  let l1 : Ghost.erased (enum_of m1.dom) = FStar.IndefiniteDescription.elim_squash m1.dom_ex in
  let l2 : Ghost.erased (enum_of m2.dom) = FStar.IndefiniteDescription.elim_squash m2.dom_ex in
  Util.union_as_list l1 l2 m2.dom;
  let l : Ghost.erased (enum_of dom) = List.Tot.append (List.Tot.filter (Util.notp m2.dom) l1) l2 in
  {
    dom = dom;
    dom_ex = ();
    dom_fold_bool = fold_of_intro_union dom m1.dom m2.dom l1 l2 _ m1.dom_fold_bool m2.dom_fold_bool;
    dom_fold_nat = fold_of_intro_union dom m1.dom m2.dom l1 l2 _ m1.dom_fold_nat m2.dom_fold_nat;
    dom_key_set = F.on_dom (key_set_dom dom) #(key_set_codom dom) (fun d ->
      let d1 : key_set_dom m1.dom = {
        dom_key_s = d.dom_key_s;
        dom_key_spec = d.dom_key_spec;
        dom_key_filter = d.dom_key_filter;
        dom_key_prop = ();
      } in
      let d2 : key_set_dom m2.dom = {
        dom_key_s = d.dom_key_s;
        dom_key_spec = d.dom_key_spec;
        dom_key_filter = d.dom_key_filter;
        dom_key_prop = ();
      } in
      S.union (m1.dom_key_set d1) (m2.dom_key_set d2)
    );
    map = F.on_dom key #(codom dom value) (fun k -> if m1.dom k then m1.map k else m2.map k);
}

let get_union m1 m2 k = ()

let length_enum_of
  (#key #value: Type)
  (m: t key value)
  (l: enum_of m.dom)
: Lemma
  (length m == List.Tot.length l)
= fold_of_elim m.dom m.dom_fold_nat (Util.list_length_as_fold_op _) l 0;
  Util.list_length_as_fold l 0

let length_disjoint_union #key #value m1 m2 =
  let l1 : Ghost.erased (enum_of m1.dom) = FStar.IndefiniteDescription.elim_squash m1.dom_ex in
  let l2 : Ghost.erased (enum_of m2.dom) = FStar.IndefiniteDescription.elim_squash m2.dom_ex in
  Util.union_as_list l1 l2 m2.dom;
  let m = union m1 m2 in
  let l : Ghost.erased (enum_of m.dom) = List.Tot.append (List.Tot.filter (Util.notp m2.dom) l1) l2 in
  Util.list_for_all_mem_filter (Util.notp m2.dom) l1;
  assert (Ghost.reveal l == List.Tot.append l1 l2);
  length_enum_of m1 l1;
  length_enum_of m2 l2;
  length_enum_of m l;
  List.Tot.append_length l1 l2

let filter_op
  (#key: Type)
  (#value: Type u#a)
  (f: (key & value) -> bool)
  (m: t key value)
  (k: key)
: Tot bool
= if m.dom k
  then f (k, m.map k)
  else false

let filter #key #value f m =
  let dom = F.on_dom key (fun k -> filter_op f m k) in
  let l : Ghost.erased (enum_of m.dom) = FStar.IndefiniteDescription.elim_squash m.dom_ex in
  Classical.forall_intro (List.Tot.mem_filter (filter_op f m) l);
  let l' : Ghost.erased (enum_of dom) = List.Tot.filter (filter_op f m) l in
  {
    dom = dom;
    dom_ex = ();
    dom_fold_bool = fold_of_intro_filter dom m.dom l (filter_op f m) _ m.dom_fold_bool;
    dom_fold_nat = fold_of_intro_filter dom m.dom l (filter_op f m) _ m.dom_fold_nat;
    dom_key_set = F.on_dom (key_set_dom dom) #(key_set_codom dom) (fun d ->
      let d' : key_set_dom m.dom = {
        dom_key_s = d.dom_key_s;
        dom_key_spec = d.dom_key_spec;
        dom_key_filter = (fun (k: key) -> filter_op f m k && d.dom_key_filter k);
        dom_key_prop = ()
      } in
      m.dom_key_set d'
    );
    map = F.on_dom key #(codom dom value)
      (fun k ->
        if m.dom k then
          let v = m.map k in
          if f (k, v)
          then v
          else UU
        else UU
      )
  }

let get_filter f m k = ()

let for_all
  #key #value f m
= let l : Ghost.erased (enum_of m.dom) = FStar.IndefiniteDescription.elim_squash m.dom_ex in
  Util.list_for_all_as_fold (filter_op f m) true l;
  List.Tot.for_all_mem (filter_op f m) l;
  m.dom_fold_bool (Util.list_for_all_as_fold_op (filter_op f m)) true
