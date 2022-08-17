module LowParse.SteelST.Fold.URef
open LowParse.Spec.Base
open LowParse.SteelST.Fold.Gen

// Do not open/include this module. Instead, use a module abbreviation.

module R = Steel.ST.Reference

inline_for_extraction
let state_i : Type = bool

let state_t (t: Type) (b: state_i) : Type = (x: option t { Some? x == b })

let sem_get (t: Type) : Tot (stt (state_t t) t true true) =
  (function Some s -> (s, Some s))

let sem_put (#t: Type) (v: t) (pre: state_i) : Tot (stt (state_t t) unit pre true) =
  (fun _ -> ((), Some v))

noeq
type action_t (t: Type) : Type -> state_i -> state_i -> Type =
| Get: action_t t t true true
| Put: (v: t) -> (pre: state_i) -> action_t t unit pre true

let action_sem (#t: Type) (#ret_t: Type) (#pre: state_i) (#post: state_i) (a: action_t t ret_t pre post) : Tot (stt (state_t t) ret_t pre post) =
  match a with
  | Get -> sem_get t
  | Put v pre -> sem_put v pre

open Steel.ST.GenElim

[@@__reduce__]
let ll_state_match
  (#t: Type)
  (r: R.ref t)
  (#i: state_i)
  (h: state_t t i)
  (_: unit)
: Tot vprop
= exists_ (fun h' -> R.pts_to r full_perm h' `star` pure (i == true ==> h == Some h'))

let cl
  (#t: Type)
  (r: R.ref t)
: Tot (low_level_state state_i (state_t t) unit unit)
= {
    ll_state_match = ll_state_match r;
    ll_state_failure = (fun _ -> pure False); // ref action implementations will never fail
    state_ge = (fun _ _ -> True);
    state_ge_refl = (fun _ -> ());
    state_ge_trans = (fun _ _ _ -> ());
    ll_state_failure_inc = (fun _ _ -> noop ());
    ll_state_shape = (fun _ _ -> True);
    ll_state_match_shape = (fun _ _ -> noop ());
    ll_state_pts_to = (fun _ _ -> emp);
  }

inline_for_extraction
let impl_get
  (#t: Type)
  (r: R.ref t)
: Tot (stt_impl_t (cl r) (sem_get t))
= fun _ (* kpre *) _ (* kpost *) st h k_success _ (* k_failure *) ->
    rewrite
      ((cl r).ll_state_match h st)
      (ll_state_match r h st);
    let _ = gen_elim () in
    let v = R.read r in
    rewrite
      (ll_state_match r h st)
      ((cl r).ll_state_match h st);
    k_success _ _ v

inline_for_extraction
let impl_put
  (#t: Type)
  (r: R.ref t)
  (v: t)
  (pre: state_i)
: Tot (stt_impl_t (cl r) (sem_put v pre))
= fun _ (* kpre *) _ (* kpost *) st h k_success _ (* k_failure *) ->
    rewrite
      ((cl r).ll_state_match h st)
      (ll_state_match r h st);
    let _ = gen_elim () in
    let h' : Ghost.erased (state_t t true) = Some v in
    R.write r v;
    rewrite
      (ll_state_match r h' st)
      ((cl r).ll_state_match h' st);
    k_success st h' ()

[@@specialize]
let impl_action
  (#t: Type)
  (r: R.ref t)
  (#rt: Type)
  (#pre: _)
  (#post: _)
  (a: action_t t rt pre post)
: Tot (stt_impl_t (cl r) (action_sem a))
= match a with
  | Get -> coerce _ (impl_get r)
  | Put v pre -> coerce _ (impl_put r v pre)

[@@specialize]
let a_cl
  (#t: Type)
  (r: R.ref t)
: Tot (action_impl (cl r) (action_t t) action_sem)
= {
    a_inc = (fun _ _ -> ());
    a_impl = impl_action r;
  }

inline_for_extraction
let with_ll_state_ptr
  (#t: Type)
  (r: R.ref t)
  (inv: state_i)
: Tot (with_ll_state_ptr_t (cl r) inv)
= fun h #kpre #t #kpost k ->
    rewrite emp ((cl r).ll_state_pts_to () h);
    let res = k () in
    let _ = gen_elim () in
    rewrite ((cl r).ll_state_pts_to _ _) emp;
    return res

inline_for_extraction
let load_ll_state_ptr
  (#t: Type)
  (r: R.ref t)
  (inv: state_i)
: Tot (load_ll_state_ptr_t (cl r) inv)
= fun _ k -> k ()

inline_for_extraction
let store_ll_state_ptr
  (#t: Type)
  (r: R.ref t)
  (inv: state_i)
: Tot (store_ll_state_ptr_t (cl r) inv)
= fun _ _ -> noop ()

[@@specialize] // ll_state_ptr_ops is not marked inline_for_extraction, so we can't do it here either
let ptr_cl
  (#t: Type)
  (r: R.ref t)
: Tot (ll_state_ptr_ops (cl r))
= {
    with_ll_state_ptr = with_ll_state_ptr r;
    load_ll_state_ptr = load_ll_state_ptr r;
    store_ll_state_ptr = store_ll_state_ptr r;
  }
