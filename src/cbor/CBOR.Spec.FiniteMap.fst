module CBOR.Spec.FiniteMap

open FStar.FunctionalExtensionality

let map (t u: Type) : Type = t ^-> option u

let map_get (#t #u: Type) (x: t) (s: map t u) : option u = s x

let map_equal
  (#t #u: Type)
  (s1 s2: map t u)
: Tot prop
= forall x . map_get x s1 == map_get x s2

let map_equal_eq_intro
  (#t #u: Type)
  (s1 s2: map t u)
: Lemma
  (requires map_equal s1 s2)
  (ensures s1 == s2)
= assert (feq s1 s2)

let map_equal_eq
  (#t #u: Type)
  (s1 s2: map t u)
: Lemma
  (map_equal s1 s2 <==> s1 == s2)
  [SMTPat (map_equal s1 s2)]
= Classical.move_requires (map_equal_eq_intro s1) s2

let fmap' (t u: Type) : Type =
  (s: map t u { exists (l: list t) . forall (x: t) . List.Tot.memP x l <==> Some? (s x) })

let map_included (#t #u: Type) (s1 s2: t -> option u) : Tot prop =
  forall (elt: t) . begin match s1 elt with
  | None -> True
  | g -> g == s2 elt
  end

let included_elem_test_codom (#t #u: Type) (x: t -> option u) (y: t -> option u) : Type =
  (z: bool { z == true <==> map_included x y})

let included_elem_test (#t #u: Type) (x: t -> option u) : Type =
  restricted_t (t -> option u) (included_elem_test_codom x)

noeq
type fmap (t u: Type) : Type = {
  s: fmap' t u;
  test: included_elem_test s;
}

let fmap_eq (#t #u: Type) : eq_test (fmap t u) =
  (fun (s1: fmap t u) -> fun (s2: fmap t u) ->
    let res : bool = s1.test s2.s && s2.test s1.s in
    if res
    then begin
      assert (s1.s `map_equal` s2.s);
      assert (feq s1.test s2.test);
      true
    end
    else false
  )

let fmap_intro
  (#t #u: Type)
  (s: t -> Tot (option u))
  (test: (t -> option u) -> Tot bool)
  (l: Ghost.erased (list t))
: Pure (fmap t u)
    (requires (
      (forall (x: t) . List.Tot.memP x l <==> Some? (s x)) /\
      (forall (s': t -> option u) . test s' <==>  map_included s s')
    ))
    (ensures (fun _ -> True))
= Classical.exists_intro (fun (l: list t) -> forall (x: t) . List.Tot.memP x l <==>  Some? (s x) ) l;
  let s0 : fmap' t u = on_dom t s in
  {
    s = s0;
    test = on_dom (t -> option u) #(included_elem_test_codom s0) (fun (s': t -> option u) -> test s');
  }

let fmap_elim
  (#t #u: Type)
  (s: fmap t u)
: Ghost (list t)
    (requires True)
    (ensures (fun l -> forall (x: t) . List.Tot.memP x l <==> Some? (s.s x)))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun (l: list t) -> forall (x: t) . List.Tot.memP x l <==> Some? (s.s x ))

let get (#t #u: Type) (x: t) (s: fmap t u) : Tot (option u) = s.s x

let equal_eq_intro
  (#t #u: Type)
  (s1 s2: fmap t u)
: Lemma
  (requires equal s1 s2)
  (ensures s1 == s2)
= assert (feq s1.s s2.s);
  assert (feq s1.test s2.test)

let equal_eq
  (#t #u: Type)
  (s1 s2: fmap t u)
: Lemma
  (equal s1 s2 <==> s1 == s2)
  [SMTPat (equal s1 s2)]
= Classical.move_requires (equal_eq_intro s1) s2

let empty (t u: Type) : Pure (fmap t u)
  (requires True)
  (ensures (fun s -> forall x . None? (get x s)))
=
  fmap_intro (fun _ -> None) (fun _ -> true) []

let singleton (#t #u: Type) (x: t) (elt: u) (eq: eq_elem_test x) (equ: eq_elem_test elt) : Pure (fmap t u)
  (requires True)
  (ensures (fun s -> get x s == Some elt /\ (forall y . (~ (x == y)) ==>  get y s == None)))
=
  fmap_intro (fun y' -> if eq y' then Some elt else None) (fun s' -> 
    match s' x with
    | None -> false
    | Some elt' -> equ elt')
  [x]

let union (#t #u: Type) (s1 s2: fmap t u) : Pure (fmap t u)
  (requires True)
  (ensures (fun s -> forall y . get y s == begin match get y s1 with
  | Some v -> Some v
  | _ -> get y s2
  end))
= let l1 = Ghost.hide (fmap_elim s1) in
  let l2 = Ghost.hide (fmap_elim s2) in
  Classical.forall_intro (FStar.List.Tot.append_memP l1 l2);
  fmap_intro (fun x -> match s1.s x with
  | None -> s2.s x
  | v -> v
  )
  (fun s' -> s1.test s' && s2.test (fun x' -> match s1.s x', s2.s x' with
  | Some _, Some v -> Some v
  | _ -> s' x'
  ))
  (l1 `List.Tot.append` l2)
