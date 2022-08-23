module LowParse.SteelST.Fold.Print
open LowParse.SteelST.Fold.Gen

// Do not open/include this module. Instead, use a module abbreviation.

inline_for_extraction
let state_i : Type = unit

let state_t (_: state_i) : Type = unit

module U8 = FStar.UInt8

noeq
type action_t : Type -> state_i -> state_i -> Type =
| PrintBool: (b: bool) -> action_t unit () ()
| PrintU8: (v: U8.t) -> action_t unit () ()
| PrintString: (s: string) -> action_t unit () ()

let action_sem (#ret_t: Type) (#pre: state_i) (#post: state_i) (a: action_t ret_t pre post) : Tot (stt state_t ret_t pre post) =
  (fun s -> ((), s))

open Steel.ST.GenElim

let cl
: low_level_state state_i state_t unit unit
= {
    ll_state_match = (fun _ _ -> emp);
    ll_state_failure = (fun _ -> pure False); // ref action implementations will never fail
    state_ge = (fun _ _ -> True);
    state_ge_refl = (fun _ -> ());
    state_ge_trans = (fun _ _ _ -> ());
    ll_state_failure_inc = (fun _ _ -> noop ());
    ll_state_shape = (fun _ _ -> True);
    ll_state_match_shape = (fun _ _ -> noop ());
    ll_state_pts_to = (fun _ _ -> emp);
  }

module P = Steel.ST.Printf

inline_for_extraction
let impl_print_bool
  (b: bool)
: Tot (stt_impl_t cl (action_sem (PrintBool b)))
= fun _ (* kpre *) _ (* kpost *) _ (* ll_state *) _ (* Ghost.erased t *) k_success _ (* k_failure *) ->
    P.print_bool b;
    k_success _ _ ()

inline_for_extraction
let impl_print_u8
  (u: U8.t)
: Tot (stt_impl_t cl (action_sem (PrintU8 u)))
= fun _ (* kpre *) _ (* kpost *) _ (* ll_state *) _ (* Ghost.erased t *) k_success _ (* k_failure *) ->
    P.print_u8 u;
    k_success _ _ ()

inline_for_extraction
let impl_print_string
  (s: string)
: Tot (stt_impl_t cl (action_sem (PrintString s)))
= fun _ (* kpre *) _ (* kpost *) _ (* ll_state *) _ (* Ghost.erased t *) k_success _ (* k_failure *) ->
    P.print_string s;
    k_success _ _ ()

[@@specialize]
let impl_action
  (#rt: Type)
  (#pre: _)
  (#post: _)
  (a: action_t rt pre post)
: Tot (stt_impl_t cl (action_sem a))
= match a with
  | PrintBool b -> impl_print_bool b
  | PrintU8 u -> impl_print_u8 u
  | PrintString s -> impl_print_string s

[@@specialize]
let a_cl
: (action_impl cl action_t action_sem)
= {
    a_inc = (fun _ _ -> ());
    a_impl = impl_action;
  }

inline_for_extraction
let with_ll_state_ptr
  (inv: state_i)
: Tot (with_ll_state_ptr_t cl inv)
= fun h #kpre #t #kpost k ->
    rewrite emp ((cl).ll_state_pts_to () h);
    let res = k () in
    let _ = gen_elim () in
    rewrite ((cl).ll_state_pts_to _ _) emp;
    return res

inline_for_extraction
let load_ll_state_ptr
  (inv: state_i)
: Tot (load_ll_state_ptr_t (cl) inv)
= fun _ k -> k ()

inline_for_extraction
let store_ll_state_ptr
  (inv: state_i)
: Tot (store_ll_state_ptr_t (cl) inv)
= fun _ _ -> noop ()

[@@specialize] // ll_state_ptr_ops is not marked inline_for_extraction, so we can't do it here either
let ptr_cl
: (ll_state_ptr_ops (cl))
= {
    with_ll_state_ptr = with_ll_state_ptr;
    load_ll_state_ptr = load_ll_state_ptr;
    store_ll_state_ptr = store_ll_state_ptr;
  }

inline_for_extraction
let mk_ll_state : mk_ll_state_t cl emp #() () =
  fun k ->
    rewrite emp (cl.ll_state_match () ());
    k ()

let elim_extract_impl_unit_post
  (#opened: _)
  (#pre #post: state_i)
  (f: stt state_t unit pre post)
  (h: state_t pre)
  (b: bool)
: STGhost unit opened
    (extract_impl_unit_post cl pre post f h b)
    (fun _ -> emp)
    True
    (fun _ -> b == true)
=
  let h' = get_return_state f h in
  if b
  then begin
    rewrite
      (extract_impl_unit_post cl pre post f h b)
      (exists_ (cl.ll_state_match h'));
    let _ = gen_elim () in
    rewrite (cl.ll_state_match _ _) emp
  end else begin
    rewrite
      (extract_impl_unit_post cl pre post f h b)
      (pure False);
    let _ = gen_elim () in
    noop ()
  end

module R = Steel.ST.Reference

let elim_extract_impl_post
  (#opened: _)
  (#pre #post: state_i)
  (#ret_t: Type)
  (r: R.ref ret_t)
  (f: stt state_t ret_t pre post)
  (h: state_t pre)
  (b: bool)
: STGhost (Ghost.erased ret_t) opened
    (extract_impl_post cl pre post r f h b)
    (fun v -> R.pts_to r full_perm v)
    True
    (fun v ->
      b == true /\
      v == get_return_value f h
    )
=
  let h' = get_return_state f h in
  let v = get_return_value f h in
  if b
  then begin
    rewrite
      (extract_impl_post cl pre post r f h b)
      (exists_ (cl.ll_state_match h') `star` R.pts_to r full_perm v);
    let _ = gen_elim () in
    rewrite (cl.ll_state_match _ _) emp;
    v
  end else begin
    rewrite
      (extract_impl_post cl pre post r f h b)
      (pure False `star` exists_ (R.pts_to r full_perm));
    let _ = gen_elim () in
    vpattern_replace_erased (R.pts_to r full_perm)
  end

let no_fail : no_ll_state_failure_t cl =
  fun h ->
    rewrite (cl.ll_state_failure h) (pure False);
    let _ = gen_elim () in
    ()
