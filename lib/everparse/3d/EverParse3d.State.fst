module EverParse3d.State
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.ForEvery

open FStar.FunctionalExtensionality

let extensionality' (a: Type) (b: (a -> Type)) (f g: restricted_t a b)
    : Lemma (requires feq #a #b f g) (ensures f == g)
= ()

let extensionality_g' (a: Type) (b: (a -> Type)) (f g: restricted_g_t a b)
    : Lemma (requires feq_g #a #b f g) (ensures f == g)
= ()

module ID = FStar.IndefiniteDescription

let arrow_g (t1: Type) (t2: Type) = t1 ^->> t2

let refine_bool_t (t: Type) (p: t `arrow_g` bool) = (x: t { p x })

let restricted_t' (a: Type) (b: a -> Type) = restricted_t a (on_dom a b)

let restricted_t'_eq (a1: Type) (b1: a1 -> Type) (a2: Type) (b2: a2 -> Type) : Lemma
  (requires
    a1 == a2 /\
    feq b1 b2
  )
  (ensures restricted_t' a1 b1 == restricted_t' a2 b2)
= ()

let arrow (t1: Type) (t2: Type) = t1 ^-> t2

[@@erasable]
noeq type state_dict = {
  state_p: string `arrow_g` bool;
  state_values: refine_bool_t string state_p `arrow` Type0;
  state: restricted_t' (refine_bool_t string state_p) (fun x -> (state_values x `arrow` slprop));
}

let state_dict_ext
  (d1 d2: state_dict)
: Lemma
  (requires (
    (forall x . d1.state_p x == d2.state_p x) /\
    (forall (x: refine_bool_t string d1.state_p) . d1.state_values x == d2.state_values x) /\
    (forall (x: refine_bool_t string d1.state_p) (v: d1.state_values x) . d1.state x v == d2.state x v
  )))
  (ensures (
    d1 == d2
  ))
= assert (feq_g (d1.state_p <: (string ^->> bool)) (d2.state_p <: (string ^->> bool)));
  extensionality_g' string (fun _ -> bool) d1.state_p d2.state_p;
  assert (d1.state_p == d2.state_p);
  assert (refine_bool_t string d1.state_p == refine_bool_t string d2.state_p);
  assert (refine_bool_t string d1.state_p `arrow` Type0 == refine_bool_t string d2.state_p `arrow` Type0);
  assert (feq d1.state_values d2.state_values);
  extensionality' (refine_bool_t string d1.state_p) (fun _ -> Type0) d1.state_values (coerce_eq () d2.state_values <: refine_bool_t string d1.state_p `arrow` Type0);
  assert (d1.state_values == d2.state_values);
  assert (forall (x: refine_bool_t string d1.state_p) . feq (d1.state x) (d2.state x));
  let prf
    (x: refine_bool_t string d1.state_p)
  : Lemma (ensures d1.state x == d2.state x)
    [SMTPat (d1.state x)]
  =
    assert (d1.state_values x `arrow` slprop == d2.state_values x `arrow` slprop);
    extensionality' (d1.state_values x) (fun _ -> slprop) (d1.state x) (coerce_eq () (d2.state x) <: d1.state_values x `arrow` slprop)
  in
  assert (forall (x: refine_bool_t string d1.state_p) . d1.state x == d2.state x);
  restricted_t'_eq
    (refine_bool_t string d1.state_p) (fun x -> (d1.state_values x `arrow` slprop))
    (refine_bool_t string d2.state_p) (fun x -> (d2.state_values x `arrow` slprop));
  assert (feq d1.state (coerce_eq () d2.state <: restricted_t' (refine_bool_t string d1.state_p) (fun x -> (d1.state_values x `arrow` slprop))));
  extensionality' (refine_bool_t string d1.state_p) (on_dom (refine_bool_t string d1.state_p) (fun x -> d1.state_values x ^-> slprop)) d1.state (coerce_eq () d2.state <: restricted_t' (refine_bool_t string d1.state_p) (fun x -> (d1.state_values x `arrow` slprop)));
  assert (d1.state == d2.state);
  assert (d1 == d2)

let mk_state_dict
  (p: string -> prop)
  (values: (x: string { p x }) -> Type0)
  (state: (x: string { p x }) -> values x -> slprop)
: Tot state_dict
=
  let p' = on_g string (fun x -> ID.strong_excluded_middle (p x) <: bool) in
  let values' = on (refine_bool_t string p') values in
  let state' (x: refine_bool_t string p') : (values' x ^-> slprop) = on (values' x) (state x) in
  {
    state_p = p';
    state_values = values';
    state = on_dom (refine_bool_t string p') state';
  }

let mk_state_dict_correct
  (p: string -> prop)
  (values: (x: string { p x }) -> Type0)
  (state: (x: string { p x }) -> values x -> slprop)
: Lemma
  (ensures (let d = mk_state_dict p values state in
    (forall x . d.state_p x == true <==> p x) /\
    (forall (x: string { p x }) . values x == d.state_values x) /\
    (forall (x: refine_bool_t string d.state_p) . d.state_values x == values x) /\
    (forall (x: refine_bool_t string d.state_p) (y: d.state_values x) . d.state x y == state x y) /\
    (forall (x: string { p x }) (y: values x) . state x y == d.state x y)
  ))
  [SMTPat (mk_state_dict p values state)]
= let d = mk_state_dict p values state in
  let prf
    (x: refine_bool_t string d.state_p)
    (y: d.state_values x)
  : Lemma
    (d.state x y == state x y)
  =
    let p' = on_g string (fun x -> ID.strong_excluded_middle (p x) <: bool) in
    assert (d.state_p == p');
    let values' : refine_bool_t string d.state_p `arrow` Type0 = on (refine_bool_t string d.state_p) values in
    assert_norm (d.state_values == (coerce_eq () values' <: (refine_bool_t string d.state_p `arrow` Type0)));
    let state' (x: refine_bool_t string p') : (d.state_values x ^-> slprop) = on (d.state_values x) (state x) in
    assert_norm (d.state == on_dom (refine_bool_t string d.state_p) state');
    assert_norm (d.state x == on_dom (refine_bool_t string d.state_p) state' x);
    assert (d.state x == state' x);
    assert (d.state x y == state' x y);
    assert (d.state x y == state x y)
  in
  Classical.forall_intro_2 prf

let mk_state_dict_ext
  (p1: string -> prop)
  (values1: (x: string { p1 x }) -> Type0)
  (state1: (x: string { p1 x }) -> values1 x -> slprop)
  (p2: string -> prop)
  (values2: (x: string { p2 x }) -> Type0)
  (state2: (x: string { p2 x }) -> values2 x -> slprop)
: Lemma
  (requires (
    (forall x . p1 x <==> p2 x) /\
    (forall (x: string { p1 x }) . values1 x == values2 x) /\
    (forall (x: string { p1 x }) (v: values1 x) . state1 x v == state2 x v)
  ))
  (ensures (mk_state_dict p1 values1 state1 == mk_state_dict p2 values2 state2))
= let d1 = mk_state_dict p1 values1 state1 in
  let d2 = mk_state_dict p2 values2 state2 in
  assert (feq_g d1.state_p d2.state_p);
  assert (feq d1.state_values d2.state_values);
  restricted_t'_eq
    (refine_bool_t string d1.state_p) (fun x -> (d1.state_values x `arrow` slprop))
    (refine_bool_t string d2.state_p) (fun x -> (d2.state_values x `arrow` slprop));
  let prf2
    (x: refine_bool_t string d1.state_p)
  : Lemma
    (d1.state x == (coerce_eq () (d2.state x) <: d1.state_values x `arrow` slprop))
  =
    assert (forall y . d1.state x y == d2.state x y);
    assert (feq (d1.state x) (coerce_eq () (d2.state x) <: d1.state_values x `arrow` slprop));
    extensionality' (d1.state_values x) (fun _ -> slprop) (d1.state x) (coerce_eq () (d2.state x) <: d1.state_values x `arrow` slprop)
  in
  Classical.forall_intro prf2;
  assert (forall (x: refine_bool_t string d1.state_p) . d1.state x == d2.state x);
  assert (feq d1.state (coerce_eq () d2.state <: restricted_t' (refine_bool_t string d1.state_p) (fun x -> (d1.state_values x `arrow` slprop))));
  state_dict_ext d1 d2

let mk_state_dict_idem
  (d: state_dict)
: Lemma
  (d == mk_state_dict
    (fun x -> d.state_p x == true)
    d.state_values
    d.state
  )
= state_dict_ext
    d
    (mk_state_dict
      (fun x -> d.state_p x == true)
      d.state_values
      d.state
    )

let state_p
  (d: state_dict)
  (x: string)
: Tot prop
= d.state_p x == true

let refine_prop_t (t: Type) (p: t `arrow` prop) = (x: t { p x })

[@@erasable]
let forevery_values0
      (p1: string -> prop)
      (values1: (x: string { p1 x }) -> Type0)
: Tot Type0
= restricted_g_t (refine_prop_t string (on_dom string p1)) (on_dom (refine_prop_t string (on_dom string p1)) values1)

[@@erasable]
let forevery_values
  (d: state_dict)
: Tot Type0
= forevery_values0 (state_p d) d.state_values

let forevery_values_ext
  (d: state_dict)
  (f1 f2: forevery_values d)
: Lemma
  (requires (
    forall (x: string { state_p d x }) . f1 x == f2 x
  ))
  (ensures (f1 == f2))
= extensionality_g'
    (refine_prop_t string (on_dom string (state_p d)))
    (on_dom (refine_prop_t string (on_dom string (state_p d))) (d.state_values))
    f1 f2

let forevery_state_body
      (d: state_dict)
      (v: forevery_values d)
      (x: string)
: Tot slprop
= if d.state_p x then d.state x (v x) else emp

let forevery_state
      (d: state_dict)
      (v: forevery_values d)
: Tot slprop
= forall+ (x: string { state_p d x }) . forevery_state_body d v x

let state_dict_empty
: state_dict =
  mk_state_dict
    (fun _ -> False)
    (fun _ -> unit)
    (fun _ _ -> emp)

unfold
let state_dict_weaken_prop0
  (d1 d2: state_dict)
: Tot prop
= (forall (x: string) . state_p d1 x ==> state_p d2 x) /\
  (forall (x: string { state_p d1 x }) . d1.state_values x == d2.state_values x) /\
  (forall (x: string { state_p d1 x }) (y: d1.state_values x) . d1.state x y == d2.state x y)

let state_dict_weaken_prop = state_dict_weaken_prop0

let forevery_singleton_prop
  (name: string)
  (x: string)
: Tot prop
= x == name

let forevery_singleton_values
  (name: string)
  (t: Type0)
  (x: string { forevery_singleton_prop name x })
: Tot Type0
= t

let forevery_singleton_state
  (name: string)
  (#t: Type0)
  (state: t -> slprop)
  (x: string { forevery_singleton_prop name x })
  (v: forevery_singleton_values name t x)
: Tot slprop
= state v

let state_dict_singleton
  (name: string)
  (#t: Type0)
  (state: t -> slprop)
: state_dict =
  mk_state_dict
    (forevery_singleton_prop name)
    (forevery_singleton_values name t)
    (forevery_singleton_state name state)

ghost fn forevery_state_dict_singleton_unfold
  (name: string)
  (#t: Type0)
  (state: t -> slprop)
  (v: forevery_values (state_dict_singleton name state))
requires
  forevery_state (state_dict_singleton name state) v
ensures
  state (v name)
{
  unfold (forevery_state (state_dict_singleton name state) v);
  forevery_remove' _ _ name;
  forevery_elim_empty _;
  rewrite (forevery_state_body (state_dict_singleton name state) v name) as (state (v name))
}

let mk_state_dict_value
  (d: state_dict)
  (f: (x: refine_prop_t string (on_dom string (state_p d))) -> GTot (d.state_values x))
: Tot (forevery_values d)
= (on_dom_g
    (refine_prop_t string (on_dom string (state_p d)))
    #(on_dom (refine_prop_t string (on_dom string (state_p d))) d.state_values)
    f
  )

let mk_singleton_value
  (name: string)
  (#t: Type0)
  (state: t -> slprop)
  (v: t)
: Tot (forevery_values (state_dict_singleton name state))
= mk_state_dict_value (state_dict_singleton name state)
    (fun x -> if x = name then v else ())

ghost fn forevery_state_dict_singleton_fold
  (name: string)
  (#t: Type0)
  (state: t -> slprop)
  (v: t)
requires
  state v
ensures
  forevery_state (state_dict_singleton name state) (mk_singleton_value name state v)
{
  rewrite (state v) as (forevery_state_body (state_dict_singleton name state) (mk_singleton_value name state v) name);
  forevery_intro_false (forevery_state_body (state_dict_singleton name state) (mk_singleton_value name state v));
  forevery_insert _ _;
  forevery_refine_ext (state_p (state_dict_singleton name state)) _;
  fold (forevery_state (state_dict_singleton name state) (mk_singleton_value name state v));
}

let state_dict_prod
  (d1 d2: state_dict)
: Pure state_dict
  (requires (forall x . ~ (d1.state_p x /\ d2.state_p x)))
  (ensures fun _ -> True)
= mk_state_dict
    (fun x -> d1.state_p x \/ d2.state_p x)
    (fun x -> if d1.state_p x then d1.state_values x else d2.state_values x)
    (fun x v -> if d1.state_p x then d1.state x v else d2.state x v)

let state_dict_prod_comm
  (d1 d2: state_dict)
: Lemma
  (requires (forall x . ~ (d1.state_p x /\ d2.state_p x)))
  (ensures (state_dict_prod d1 d2 == state_dict_prod d2 d1))
= mk_state_dict_ext
    (fun x -> d1.state_p x \/ d2.state_p x)
    (fun x -> if d1.state_p x then d1.state_values x else d2.state_values x)
    (fun x v -> if d1.state_p x then d1.state x v else d2.state x v)
    (fun x -> d2.state_p x \/ d1.state_p x)
    (fun x -> if d2.state_p x then d2.state_values x else d1.state_values x)
    (fun x v -> if d2.state_p x then d2.state x v else d1.state x v)

let state_dict_prod_empty
  (d: state_dict)
: Lemma
  (state_dict_prod d state_dict_empty == d)
= assert_norm (state_dict_prod d state_dict_empty == mk_state_dict
    (fun x -> d.state_p x \/ state_dict_empty.state_p x)
    (fun x -> if d.state_p x then d.state_values x else state_dict_empty.state_values x)
    (fun x v -> if d.state_p x then d.state x v else state_dict_empty.state x v)
  );
  mk_state_dict_ext
    (fun x -> d.state_p x \/ state_dict_empty.state_p x)
    (fun x -> if d.state_p x then d.state_values x else state_dict_empty.state_values x)
    (fun x v -> if d.state_p x then d.state x v else state_dict_empty.state x v)
    (fun x -> d.state_p x == true)
    d.state_values
    d.state;
 mk_state_dict_idem d

#push-options "--z3rlimit 32"

let state_dict_prod_assoc
  (d1 d2 d3: state_dict)
: Lemma
  (requires (
    (forall x . ~ (d1.state_p x /\ d2.state_p x)) /\
    (forall x . ~ ((d1.state_p x \/ d2.state_p x) /\ d3.state_p x))
  ))
  (ensures (
    (d1 `state_dict_prod` d2) `state_dict_prod` d3 ==
    d1 `state_dict_prod` (d2 `state_dict_prod` d3)
  ))
= let d12 = d1 `state_dict_prod` d2 in
  let d23 = d2 `state_dict_prod` d3 in
  assert_norm (d1 `state_dict_prod` d23 == mk_state_dict
    (fun x -> d1.state_p x \/ d23.state_p x)
    (fun x -> if d1.state_p x then d1.state_values x else d23.state_values x)
    (fun x v -> if d1.state_p x then d1.state x v else d23.state x v)
  );
  assert_norm (d12 `state_dict_prod` d3 == mk_state_dict
    (fun x -> d12.state_p x \/ d3.state_p x)
    (fun x -> if d12.state_p x then d12.state_values x else d3.state_values x)
    (fun x v -> if d12.state_p x then d12.state x v else d3.state x v)
  );
  mk_state_dict_ext
    (fun x -> d1.state_p x \/ d23.state_p x)
    (fun x -> if d1.state_p x then d1.state_values x else d23.state_values x)
    (fun x v -> if d1.state_p x then d1.state x v else d23.state x v)
    (fun x -> d12.state_p x \/ d3.state_p x)
    (fun x -> if d12.state_p x then d12.state_values x else d3.state_values x)
    (fun x v -> if d12.state_p x then d12.state x v else d3.state x v);
  assert (
    (d1 `state_dict_prod` d2) `state_dict_prod` d3 ==
    d1 `state_dict_prod` (d2 `state_dict_prod` d3)
  )

#pop-options

let mk_prod_value
  (#d1 #d2: state_dict)
  (f1: forevery_values d1)
  (f2: forevery_values d2)
  (_: squash (forall x . ~ (d1.state_p x /\ d2.state_p x)))
: Tot (forevery_values (state_dict_prod d1 d2))
= mk_state_dict_value (state_dict_prod d1 d2)
    (fun x -> if d1.state_p x then f1 x else f2 x)

let mk_proj_value
  (#d: state_dict)
  (f: forevery_values d)
  (d': state_dict)
  (_: squash (state_dict_weaken_prop d' d))
: Tot (forevery_values d')
= mk_state_dict_value d' (fun x -> f x)

let state_dict_weaken_prod
  (d1 d2: state_dict)
: Lemma
  (requires
    (forall x . ~ (d1.state_p x /\ d2.state_p x))
  )
  (ensures (
    state_dict_weaken_prop d1 (state_dict_prod d1 d2) /\
    state_dict_weaken_prop d2 (state_dict_prod d1 d2)
  ))
  [SMTPat (state_dict_prod d1 d2)]
= assert (state_dict_weaken_prop0 d1 (state_dict_prod d1 d2));
  assert (state_dict_weaken_prop0 d2 (state_dict_prod d1 d2))  

ghost
fn forevery_when_split
  (#a:Type0)
  (p: a -> slprop)
  (f: a -> prop)
  (g: a -> prop)
  requires
    forall+ (x:a). when_ (f x /\ g x) (p x)
  ensures
    forall+ (x:a). when_ (f x) (when_ (g x) (p x))
{
  forevery_map #a (fun x -> when_ (f x /\ g x) (p x)) (fun x -> when_ (f x) (when_ (g x) (p x))) fn x {
    rewrite when_ (f x /\ g x) (p x)
    as when_ (f x) (when_ (g x) (p x))
  }
}

ghost
fn forevery_when_join
  (#a:Type0)
  (p: a -> slprop)
  (f: a -> prop)
  (g: a -> prop)
  requires
    forall+ (x:a). when_ (f x) (when_ (g x) (p x))
  ensures
    forall+ (x:a). when_ (f x /\ g x) (p x)
{
  forevery_map #a (fun x -> when_ (f x) (when_ (g x) (p x))) (fun x -> when_ (f x /\ g x) (p x)) fn x {
    rewrite when_ (f x) (when_ (g x) (p x))
    as when_ (f x /\ g x) (p x)
  }
}

ghost
fn forevery_refine_split'
  (#a:Type0)
  (p: a -> slprop)
  (f: a -> prop)
  (g: a -> prop)
  requires
    forall+ (x:a{f x}). p x
  ensures
    forall+ (x:a{f x /\ g x}). p x
  ensures
    forall+ (x:a{f x /\ ~ (g x)}). p x
{
  forevery_unrefine_pred _ _;
  forevery_refine_split _ g;
  forevery_unrefine_pred (fun x -> when_ (f x) (p x)) (fun x -> g x);
  forevery_when_join _ _ _;
  forevery_refine_pred _ (fun x -> g x /\ f x);
  forevery_refine_ext' (fun x -> f x /\ g x) p;
  forevery_unrefine_pred (fun x -> when_ (f x) (p x)) (fun x -> ~ (g x));
  forevery_when_join _ _ _;
  forevery_refine_pred _ (fun x -> (~ (g x)) /\ f x);
  forevery_refine_ext' #_ #(fun x -> (~ (g x)) /\ f x) (fun x -> f x /\ ~ (g x)) p;
}

ghost fn forevery_state_dict_prod_unfold
  (#d1: state_dict)
  (#d2: state_dict)
  (_: squash (forall x . ~ (d1.state_p x /\ d2.state_p x)))
  (v: forevery_values (state_dict_prod d1 d2))
requires
  forevery_state (state_dict_prod d1 d2) v
ensures
  forevery_state d1 (mk_proj_value v d1 ()) **
  forevery_state d2 (mk_proj_value v d2 ())
{
  unfold (forevery_state (state_dict_prod d1 d2) v);
  forevery_refine_split' _ _ (state_p d1);
  forevery_refine_ext' #_ #(fun x -> state_p (state_dict_prod d1 d2) x /\ state_p d1 x) (state_p d1) _;
  forevery_map #(x: string { state_p d1 x }) (fun x -> forevery_state_body (state_dict_prod d1 d2) v x) (fun x -> forevery_state_body d1 (mk_proj_value v d1 ()) x) fn x {
    rewrite forevery_state_body (state_dict_prod d1 d2) v x
    as forevery_state_body d1 (mk_proj_value v d1 ()) x
  };
  fold (forevery_state d1 (mk_proj_value v d1 ()));
  forevery_refine_ext' #_ #(fun x -> state_p (state_dict_prod d1 d2) x /\ ~ (state_p d1 x)) (state_p d2) _;
  forevery_map #(x: string { state_p d2 x }) (fun x -> forevery_state_body (state_dict_prod d1 d2) v x) (fun x -> forevery_state_body d2 (mk_proj_value v d2 ()) x) fn x {
    rewrite forevery_state_body (state_dict_prod d1 d2) v x
    as forevery_state_body d2 (mk_proj_value v d2 ()) x
  };
  fold (forevery_state d2 (mk_proj_value v d2 ()));
}

ghost fn forevery_state_dict_prod_fold
  (#d1: state_dict)
  (#d2: state_dict)
  (v1: forevery_values d1)
  (v2: forevery_values d2)
  (_: squash (forall x . ~ (d1.state_p x /\ d2.state_p x)))
requires
  forevery_state d1 v1 **
  forevery_state d2 v2
ensures
  forevery_state (state_dict_prod d1 d2) (mk_prod_value v1 v2 ())
{
  unfold (forevery_state d1 v1);
  forevery_map #(x: string { state_p d1 x }) (fun x -> forevery_state_body d1 v1 x) (fun x -> forevery_state_body (state_dict_prod d1 d2) (mk_prod_value v1 v2 ()) x)  fn x {
    rewrite forevery_state_body d1 v1 x
    as forevery_state_body (state_dict_prod d1 d2) (mk_prod_value v1 v2 ()) x
  };
  unfold (forevery_state d2 v2);
  forevery_map #(x: string { state_p d2 x }) (fun x -> forevery_state_body d2 v2 x) (fun x -> forevery_state_body (state_dict_prod d1 d2) (mk_prod_value v1 v2 ()) x)  fn x {
    rewrite forevery_state_body d2 v2 x
    as forevery_state_body (state_dict_prod d1 d2) (mk_prod_value v1 v2 ()) x
  };
  forevery_refine_join _ (state_p d1) (state_p d2);
  forevery_refine_ext' (state_p (state_dict_prod d1 d2)) _;
  fold (forevery_state (state_dict_prod d1 d2) (mk_prod_value v1 v2 ()))
}
