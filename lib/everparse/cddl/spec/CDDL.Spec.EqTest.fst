module CDDL.Spec.EqTest
module FE = FStar.FunctionalExtensionality

let eq_test_for (#t: Type) (x1: t) : Type =
  FE.restricted_t t (fun x2 -> (y: bool { y == true <==> x1 == x2 }))

let eq_test (t: Type) : Type =
  FE.restricted_t t (fun x1 -> eq_test_for x1)

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

let eqtype_eq (t: eqtype) : Tot (eq_test t) =
  mk_eq_test (fun x1 x2 -> x1 = x2)

noextract
let rec list_eq'
  (#t: Type)
  (t_eq: eq_test t)
  (x1: list t)
  (x2: list t)
: Pure bool True (fun b -> b == true <==> x1 == x2)
  (decreases x1)
= match x1, x2 with
  | [], [] -> true
  | a1 :: q1, a2 :: q2 -> t_eq a1 a2 && list_eq' t_eq q1 q2
  | _ -> false

noextract
let list_eq
  (#t: Type)
  (t_eq: eq_test t)
: Tot (eq_test (list t))
= mk_eq_test (fun l1 l2 -> list_eq' t_eq l1 l2)

noextract
let option_eq
  (#t: Type)
  (t_eq: eq_test t)
: Tot (eq_test (option t))
= mk_eq_test (fun x1 x2 ->
    begin match x1, x2 with
    | None, None -> true
    | Some x1', Some x2' -> t_eq x1' x2'
    | _ -> false
    end
  )

noextract
let pair_eq
  (#t1 #t2: Type)
  (t1_eq: eq_test t1)
  (t2_eq: eq_test t2)
: Tot (eq_test (t1 & t2))
= mk_eq_test (fun x1 x2 ->
    let (x11, x12) = x1 in
    let (x21, x22) = x2 in
    t1_eq x11 x21 && t2_eq x12 x22
  )

noextract
let either_eq
  (#t1 #t2: Type)
  (t1_eq: eq_test t1)
  (t2_eq: eq_test t2)
: Tot (eq_test (either t1 t2))
= mk_eq_test (fun x1 x2 ->
    begin match x1, x2 with
    | Inl x1', Inl x2' -> t1_eq x1' x2'
    | Inr x1', Inr x2' -> t2_eq x1' x2'
    | _ -> false
    end
  )
  
module Map = CDDL.Spec.Map

noextract
let map_eq
  (t1 #t2: Type)
  (t2_eq: eq_test t2)
: eq_test (Map.t t1 t2)
= mk_eq_test (fun x1 x2 ->
    Map.equal_bool #t1 t2_eq x1 x2
  )

let map_singleton
  (#key: Type)
  (#value: Type u#a)
  (k: key)
  (k_eq: eq_test_for k)
  (v: value)
: Map.t key value
= Map.singleton k k_eq v

let map_set
  (#key: Type)
  (#value: Type)
  (m: Map.t key value)
  (k: key)
  (k_eq: eq_test_for k)
  (v: value)
: Tot (Map.t key value)
= Map.set m k k_eq v

let map_set_post
  (#key: Type)
  (#value: Type)
  (m: Map.t key value)
  (k: key)
  (k_eq: eq_test_for k)
  (v: value)
  (k' : key)
: Lemma
  (ensures (
    let m' = map_set m k k_eq v in
    Map.get m' k' == (if k_eq k' then Some v else Map.get m k')
  ))
  [SMTPat (Map.get (map_set m k k_eq v) k')]
= ()

