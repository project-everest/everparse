module LowParse.SteelST.Fold.Hoare
open LowParse.SteelST.Fold.Gen
open Steel.ST.GenElim

[@specialize]
noeq
type state_i (#state_i0: Type) (state_t: (state_i0 -> Type)) =
  {
    i: state_i0;
    p: (state_t i -> prop);
  }

let state_t (#state_i0: Type) (state_t0: (state_i0 -> Type)) (i: state_i state_t0) : Tot Type =
  (x: state_t0 i.i { i.p x })

let sem_act_post
  (#state_i0: Type) (#state_t0: (state_i0 -> Type))
  (#ret_t: Type) (#pre: state_i0) (#post: state_i0)
  (f: stt state_t0 ret_t pre post)
  (ppre: (state_t0 pre -> prop))
  (y: state_t0 post)
: Tot prop
= exists x . ppre x /\ sndp (f x) == y

inline_for_extraction
let act_ret_t
  (#state_i0: Type) (#state_t0: (state_i0 -> Type))
  (#ret_t: Type) (#pre: state_i0) (#post: state_i0)
  (f: stt state_t0 ret_t pre post)
  (ppre: (state_t0 pre -> prop))
: Tot Type
= (y: ret_t { exists h . ppre h /\ fstp (f h) == y })

let sem_act
  (#state_i0: Type) (#state_t0: (state_i0 -> Type))
  (#ret_t: Type) (#pre: state_i0) (#post: state_i0)
  (f: stt state_t0 ret_t pre post)
  (ppre: (state_t0 pre -> prop))
: Tot (stt (state_t state_t0) (act_ret_t f ppre) ({ i = pre; p = ppre }) ({ i = post; p = sem_act_post f ppre}))
= fun h ->
    let (y, h') = f h in
    (y, h')

let sem_weaken
  (#state_i0: Type) (#state_t0: (state_i0 -> Type))
  (i: state_i0)
  (pre post: (state_t0 i -> prop))
  (sq: squash (forall h . pre h ==> post h))
: Tot (stt (state_t state_t0) unit ({ i = i; p = pre }) ({ i = i; p = post }))
= fun h -> ((), h)

let sem_assert
  (#state_i0: Type) (#state_t0: (state_i0 -> Type))
  (i: state_i0)
  (p: (state_t0 i -> prop))
  (q: prop)
  (sq: squash (forall h . p h ==> q))
: Tot (stt (state_t state_t0) (squash q) ({ i = i; p = p }) ({ i = i; p = p }))
= fun h -> ((), h)

[@specialize]
noeq
type action_t
  (#state_i0: Type) (#state_t0: (state_i0 -> Type))
  (#action_t0: (Type -> state_i0 -> state_i0 -> Type))
  (action_sem0: ((#ret_t: Type) -> (#pre: state_i0) -> (#post: state_i0) -> (a: action_t0 ret_t pre post) -> stt state_t0 ret_t pre post))
: Type -> state_i state_t0 -> state_i state_t0 -> Type
= | Act:
      (#t: Type) ->
      (#pre: state_i0) ->
      (#post: state_i0) ->
      (a: action_t0 t pre post) ->
      (ppre: (state_t0 pre -> prop)) ->
      action_t action_sem0 (act_ret_t (action_sem0 a) ppre) ({ i = pre; p = ppre }) ({ i = post; p = sem_act_post (action_sem0 a) ppre})
  | Weaken:
      (i: state_i state_t0) ->
      (post: (state_t0 i.i -> prop)) ->
      (sq: squash (forall h . i.p h ==> post h)) ->
      action_t action_sem0 unit i ({i = i.i; p = post})
  | Assert:
      (i: state_i state_t0) ->
      (q: prop) ->
      (sq: squash (forall h . i.p h ==> q)) ->
      action_t action_sem0 (squash q) i i

let action_sem
  (#state_i0: Type) (#state_t0: (state_i0 -> Type))
  (#action_t0: (Type -> state_i0 -> state_i0 -> Type))
  (action_sem0: ((#ret_t: Type) -> (#pre: state_i0) -> (#post: state_i0) -> (a: action_t0 ret_t pre post) -> stt state_t0 ret_t pre post))
  (#t: Type)
  (#pre #post: state_i state_t0)
  (a: action_t action_sem0 t pre post)
: Tot (stt (state_t state_t0) t pre post)
= match a with
  | Act a ppre -> sem_act (action_sem0 a) ppre
  | Weaken i post sq -> sem_weaken i.i i.p post sq
  | Assert i q sq -> sem_assert i.i i.p q sq

let cl
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
: Tot (low_level_state (state_i state_t0) (state_t state_t0) ll_state ll_state_ptr)
= {
    ll_state_match = (fun #i (h: state_t state_t0 i) out -> cl0.ll_state_match #i.i h out);
    ll_state_failure = (fun #i h -> cl0.ll_state_failure #i.i h);
    state_ge = (fun #i1 h1 #i2 h2 -> cl0.state_ge #i1.i h1 #i2.i h2);
    state_ge_refl = (fun #i h -> cl0.state_ge_refl #i.i h);
    state_ge_trans = (fun #i1 h1 #i2 h2 #i3 h3 -> cl0.state_ge_trans #i1.i h1 #i2.i h2 #i3.i h3);
    ll_state_failure_inc = (fun #_ #i1 h1 #i2 h2 -> cl0.ll_state_failure_inc #_ #i1.i h1 #i2.i h2);
    ll_state_shape = (fun i l -> cl0.ll_state_shape i.i l);
    ll_state_match_shape = (fun #_ #i h l ->
      cl0.ll_state_match_shape #_ #i.i h l
    );
    ll_state_pts_to = cl0.ll_state_pts_to;
  }

inline_for_extraction
let impl_act
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (#ret_t: Type) (pre: Ghost.erased state_i0) (post: Ghost.erased state_i0)
  (f: Ghost.erased (stt state_t0 ret_t (Ghost.reveal pre) (Ghost.reveal post)))
  (fi: stt_impl_t cl0 f)
  (ppre: (state_t0 pre -> prop))
: Tot (stt_impl_t (cl cl0) (sem_act f ppre))
= fun kpre kpost out h k_success k_failure ->
    let h0 : Ghost.erased (state_t0 (Ghost.reveal pre)) = Ghost.hide (Ghost.reveal h) in
    rewrite
      ((cl cl0).ll_state_match _ _)
      (cl0.ll_state_match h0 out);
    fi kpre kpost _ _
      (fun out' h0' v0' ->
        let h' : Ghost.erased (state_t state_t0 ({i=Ghost.reveal post; p=sem_act_post f ppre})) = Ghost.hide (Ghost.reveal h0') in
        rewrite
          (cl0.ll_state_match _ _)
          ((cl cl0).ll_state_match h' out');
        k_success _ _ v0'
      )
      (fun (h0': Ghost.erased (state_t0 (Ghost.reveal post))) (v0': Ghost.erased ret_t) ->
        let h' : Ghost.erased (state_t state_t0 ({i=Ghost.reveal post; p=sem_act_post f ppre})) = Ghost.hide (Ghost.reveal h0') in
        let v' : Ghost.erased (act_ret_t f ppre) = Ghost.hide (Ghost.reveal v0') in
        rewrite
          (cl0.ll_state_failure _)
          ((cl cl0).ll_state_failure h');
        k_failure _ v'
      )

inline_for_extraction
let impl_weaken
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (i: Ghost.erased state_i0)
  (pre post: (state_t0 i -> prop))
  (sq: squash (forall h . pre h ==> post h))
: Tot (stt_impl_t (cl cl0) (sem_weaken (Ghost.reveal i) pre post sq))
= fun kpre kpost out h k_success k_failure ->
    let h' : Ghost.erased (state_t state_t0 ({i=Ghost.reveal i; p=post})) = Ghost.hide (Ghost.reveal h) in
    rewrite
      ((cl cl0).ll_state_match h out)
      ((cl cl0).ll_state_match h' out);
    k_success _ _ ()

inline_for_extraction
let impl_assert
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (i: Ghost.erased state_i0)
  (p: (state_t0 i -> prop))
  (q: prop)
  (sq: squash (forall h . p h ==> q))
: Tot (stt_impl_t (cl cl0) (sem_assert (Ghost.reveal i) p q sq))
= fun kpre kpost out h k_success k_failure ->
    assert (p h);
    k_success _ _ ()

[@specialize]
let a_impl
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (#action_t0: (Type -> state_i0 -> state_i0 -> Type))
  (#action_sem0: ((#ret_t: Type) -> (#pre: state_i0) -> (#post: state_i0) -> (a: action_t0 ret_t pre post) -> stt state_t0 ret_t pre post))
  (a_impl0: ((#ret_t: Type) -> (#pre: state_i0) -> (#post: state_i0) -> (a: action_t0 ret_t pre post) -> stt_impl_t cl0 (action_sem0 a)))
  (#ret_t: Type)
  (#pre: state_i state_t0)
  (#post: state_i state_t0)
  (a: action_t action_sem0 ret_t pre post)
: Tot (stt_impl_t (cl cl0) (action_sem action_sem0 a))
= match a with
  | Act a ppre -> LowParse.Spec.Base.coerce _ (impl_act #state_i0 #state_t0 #ll_state #ll_state_ptr #cl0 (Ghost.hide pre.i) (Ghost.hide post.i) (Ghost.hide (action_sem0 a))  (coerce _ (a_impl0 a)) ppre)
  | Weaken i post sq -> LowParse.Spec.Base.coerce _ (impl_weaken cl0 i.i i.p post sq)
  | Assert i q sq -> LowParse.Spec.Base.coerce _ (impl_assert cl0 i.i i.p q sq)

[@@specialize]
let a_cl
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (#action_t0: (Type -> state_i0 -> state_i0 -> Type))
  (#action_sem0: ((#ret_t: Type) -> (#pre: state_i0) -> (#post: state_i0) -> (a: action_t0 ret_t pre post) -> stt state_t0 ret_t pre post))
  (#a_cl0: action_impl cl0 action_t0 action_sem0)
: Tot (action_impl (cl cl0) (action_t action_sem0) (action_sem action_sem0))
= {
    a_inc = (fun (#t: Type)
      (#pre: state_i state_t0)
      (#post: state_i state_t0)
      (a: action_t action_sem0 t pre post)
      (s: state_t state_t0 pre) ->
      match a with
      | Act a ppre -> a_cl0.a_inc a s
      | _ -> cl0.state_ge_refl s
    );
    a_impl = a_impl a_cl0.a_impl;
  }

inline_for_extraction
let with_ll_state_ptr
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (i: Ghost.erased (state_i state_t0))
  (w: with_ll_state_ptr_t cl0 i.i)
: Tot (with_ll_state_ptr_t (cl cl0) i)
= fun l k -> 
  w l (fun p ->
    rewrite
      (cl0.ll_state_pts_to p l)
      ((cl cl0).ll_state_pts_to p l);
    let res = k p in
    let h = elim_exists () in
    rewrite
      ((cl cl0).ll_state_pts_to p h)
      (cl0.ll_state_pts_to p h);
    return res
  )

inline_for_extraction
let load_ll_state_ptr
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (i: Ghost.erased (state_i state_t0))
  (w: load_ll_state_ptr_t cl0 i.i)
: Tot (load_ll_state_ptr_t (cl cl0) i)
= fun #gl p k ->
    rewrite
      ((cl cl0).ll_state_pts_to p gl)
      (cl0.ll_state_pts_to p gl);
    w #gl p (fun l ->
      rewrite
        (cl0.ll_state_pts_to p l)
        ((cl cl0).ll_state_pts_to p l);
      k l
    )

inline_for_extraction
let store_ll_state_ptr
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (i: Ghost.erased (state_i state_t0))
  (w: store_ll_state_ptr_t cl0 i.i)
: Tot (store_ll_state_ptr_t (cl cl0) i)
= fun #gl p l' ->
    rewrite
      ((cl cl0).ll_state_pts_to p gl)
      (cl0.ll_state_pts_to p gl);
    w #gl p l';
    rewrite
      (cl0.ll_state_pts_to p l')
      ((cl cl0).ll_state_pts_to p l') 

[@@specialize]
let ptr_cl
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (ptr_cl0: ll_state_ptr_ops cl0)
: Tot (ll_state_ptr_ops (cl cl0))
= {
    with_ll_state_ptr = (fun (i: state_i state_t0) -> with_ll_state_ptr i (ptr_cl0.with_ll_state_ptr i.i));
    load_ll_state_ptr = (fun (i: state_i state_t0) -> load_ll_state_ptr i (ptr_cl0.load_ll_state_ptr i.i));
    store_ll_state_ptr = (fun i -> store_ll_state_ptr i (ptr_cl0.store_ll_state_ptr i.i));
  }

inline_for_extraction
let mk_ll_state
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (#vpre: vprop)
  (#pre: Ghost.erased (state_i state_t0))
  (h: Ghost.erased (state_t state_t0 pre))
  (mk: mk_ll_state_t cl0 vpre #pre.i h)
: Tot (mk_ll_state_t (cl cl0) vpre h)
= fun k ->
    mk (fun out ->
      rewrite
        (cl0.ll_state_match _ _)
        ((cl cl0).ll_state_match h out);
      k _
    )

inline_for_extraction
let mk_ll_state0
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (#vpre: vprop)
  (#pre: Ghost.erased state_i0)
  (#h: Ghost.erased (state_t0 pre))
  (mk: mk_ll_state_t cl0 vpre #pre (Ghost.reveal h))
  (ppre: (state_t0 pre -> prop))
  (sq: squash (ppre h))
: Tot (mk_ll_state_t (cl cl0) vpre #({i=Ghost.reveal pre; p=ppre}) h)
= [@inline_let] // this is a nasty one
  let h' : Ghost.erased (state_t state_t0 ({i=Ghost.reveal pre; p=ppre})) = Ghost.hide (Ghost.reveal h) in
  coerce _ (mk_ll_state #_ #_ #_ #_ #cl0 #vpre #({i = Ghost.reveal pre; p = ppre }) h' (coerce _ mk))

inline_for_extraction
let mk_ll_state_eq
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (#vpre: vprop)
  (#pre: Ghost.erased state_i0)
  (#h: Ghost.erased (state_t0 (Ghost.reveal pre)))
  (mk: mk_ll_state_t cl0 vpre (Ghost.reveal h))
: Tot (mk_ll_state_t (cl cl0) vpre #({i=Ghost.reveal pre; p=(fun h' -> h' == Ghost.reveal h)}) (Ghost.reveal h))
= mk_ll_state0 mk (fun h' -> h' == Ghost.reveal h) ()

let no_fail
  (#state_i0: Type) (#state_t0: (state_i0 -> Type)) (#ll_state: _) (#ll_state_ptr: _)
  (#cl0: low_level_state state_i0 state_t0 ll_state ll_state_ptr)
  (no_fail0: no_ll_state_failure_t cl0)
: Tot (no_ll_state_failure_t (cl cl0))
= fun h ->
    rewrite
      ((cl cl0).ll_state_failure h)
      (cl0.ll_state_failure h);
    no_fail0 _
