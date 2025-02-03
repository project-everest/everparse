module CDDL.Spec.EqTest
module FE = FStar.FunctionalExtensionality

let eq_test (t: Type) : Type =
  FE.restricted_t t (fun x1 -> FE.restricted_t t (fun x2 -> (y: bool { y == true <==> x1 == x2 })))

let feq2 (#t1 #t2 #t: Type) (f g: (t1 -> t2 -> t)) : Tot prop =
  forall x1 x2 . f x1 x2 == g x1 x2

let feq_intro
  (#t: Type)
  (#t': t -> Type)
  (f1 f2: FE.restricted_t t t')
  (prf: (x: t) -> Lemma
    (f1 x == f2 x)
  )
: Lemma
  (f1 == f2)
= Classical.forall_intro prf;
  assert (FE.feq f1 f2)

let eq_test_unique (#t: Type) (f1 f2: eq_test t) : Lemma
  (f1 == f2)
= feq_intro f1 f2 (fun x -> feq_intro (f1 x) (f2 x) (fun _ -> ()))

let mk_eq_test (#t: Type) (phi: ((x1: t) -> (x2: t) -> Pure bool True (fun res -> res == true <==> x1 == x2))) : Tot (eq_test t) =
  FE.on_dom t (fun x1 -> FE.on_dom t (fun x2 -> phi x1 x2 <: (y: bool { y == true <==> x1 == x2 })))
