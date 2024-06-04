module CBOR.Spec.FiniteSet

open FStar.FunctionalExtensionality

let set (t: Type) : Type = t ^-> bool

let set_mem (#t: Type) (x: t) (s: set t) : Tot bool = s x

let set_equal
  (#t: Type)
  (s1 s2: set t)
: Tot prop
= forall x . set_mem x s1 <==> set_mem x s2

let set_equal_eq_intro
  (#t: Type)
  (s1 s2: set t)
: Lemma
  (requires set_equal s1 s2)
  (ensures s1 == s2)
= assert (feq s1 s2)

let set_equal_eq
  (#t: Type)
  (s1 s2: set t)
: Lemma
  (set_equal s1 s2 <==> s1 == s2)
  [SMTPat (set_equal s1 s2)]
= Classical.move_requires (set_equal_eq_intro s1) s2

let fset' (t: Type) : Type =
  (s: set t { exists (l: list t) . forall (x: t) . List.Tot.memP x l <==> s x })

let included_elem_test_codom (#t: Type) (x: fset' t) (y: fset' t) : Type =
  (z: bool { z == true <==> (forall (elt: t) . set_mem elt x ==> set_mem elt y) })

let included_elem_test (#t: Type) (x: fset' t) : Type =
  restricted_t (fset' t) (included_elem_test_codom x)

noeq
type fset (t: Type) : Type = {
  s: fset' t;
  test: included_elem_test s;
}

let fset_eq (#t: Type) : eq_test (fset t) =
  (fun (s1: fset t) -> fun (s2: fset t) ->
    let res : bool = s1.test s2.s && s2.test s1.s in
    if res
    then begin
      assert (s1.s `set_equal` s2.s);
      assert (feq s1.test s2.test);
      true
    end
    else false
  )

let fset_intro
  (#t: Type)
  (s: t -> Tot bool)
  (test: fset' t -> Tot bool)
  (l: Ghost.erased (list t))
: Pure (fset t)
    (requires (
      (forall (x: t) . List.Tot.memP x l <==> s x) /\
      (forall (s': fset' t) . test s' <==> (forall (x: t) . s x ==> s' x))
    ))
    (ensures (fun _ -> True))
= Classical.exists_intro (fun (l: list t) -> forall (x: t) . List.Tot.memP x l <==> s x ) l;
  let s0 : fset' t = on_dom t s in
  {
    s = s0;
    test = on_dom (fset' t) #(included_elem_test_codom s0) (fun (s': fset' t) -> test s');
  }

let fset_elim
  (#t: Type)
  (s: fset t)
: Ghost (list t)
    (requires True)
    (ensures (fun l -> forall (x: t) . List.Tot.memP x l <==> s.s x))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun (l: list t) -> forall (x: t) . List.Tot.memP x l <==> s.s x )

let mem (#t: Type) (x: t) (s: fset t) : Tot bool = s.s x

let equal_eq_intro
  (#t: Type)
  (s1 s2: fset t)
: Lemma
  (requires equal s1 s2)
  (ensures s1 == s2)
= assert (feq s1.s s2.s);
  assert (feq s1.test s2.test)

let equal_eq
  (#t: Type)
  (s1 s2: fset t)
: Lemma
  (equal s1 s2 <==> s1 == s2)
  [SMTPat (equal s1 s2)]
= Classical.move_requires (equal_eq_intro s1) s2

let empty (t: Type) : Pure (fset t)
  (requires True)
  (ensures (fun s -> forall x . ~ (mem x s)))
=
  fset_intro (fun _ -> false) (fun _ -> true) []

let singleton (#t: Type) (x: t) (eq: eq_elem_test x) : Pure (fset t)
  (requires True)
  (ensures (fun s -> forall y . mem y s <==> x == y))
=
  fset_intro eq (fun s' -> s' x) [x]

let union (#t: Type) (s1 s2: fset t) : Pure (fset t)
  (requires True)
  (ensures (fun s -> forall y . mem y s <==> (mem y s1 \/ mem y s2)))
=
  let l1 = Ghost.hide (fset_elim s1) in
  let l2 = Ghost.hide (fset_elim s2) in
  Classical.forall_intro (FStar.List.Tot.append_memP l1 l2);
  fset_intro (fun x -> s1.s x || s2.s x) (fun s' -> s1.test s' && s2.test s') (l1 `List.Tot.append` l2)
