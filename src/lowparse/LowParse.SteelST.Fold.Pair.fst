module LowParse.SteelST.Fold.Pair
open LowParse.SteelST.Fold.Gen
open Steel.ST.GenElim

#set-options "--ide_id_info_off"

[@@specialize]
inline_for_extraction
let fstp
  (#t1 #t2: Type)
  (x: (t1 & t2))
: Tot t1
= match x with (x, _) -> x

[@@specialize]
inline_for_extraction
let sndp
  (#t1 #t2: Type)
  (x: (t1 & t2))
: Tot t2
= match x with (_, x) -> x

[@@specialize]
inline_for_extraction
let curry_boole_proj (#t1 #t2: Type) (p: (t1 & t2)) (b: bool) : Tot (if b then t1 else t2) =
  if b then (fstp p) else (sndp p)

let state_t
  (#state_i1: Type)
  (state_t1: (state_i1 -> Type))
  (#state_i2: Type)
  (state_t2: (state_i2 -> Type))
  (x: (state_i1 & state_i2))
: Type
= (state_t1 (fstp x) & state_t2 (sndp x))

[@@__reduce__]
let ll_state_match
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#i: (state_i1 & state_i2))
  (h: state_t state_t1 state_t2 i)
  (s: (ll_state1 & ll_state2))
: Tot vprop
= cl1.ll_state_match (fstp h) (fstp s) `star`
  cl2.ll_state_match (sndp h) (sndp s)

let choose_cl
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (b: bool)
: Tot (low_level_state (if b then state_i1 else state_i2) (if b then state_t1 else state_t2) (if b then ll_state1 else ll_state2) (if b then ll_state_ptr1 else ll_state_ptr2))
= if b then cl1 else cl2

let notp (b: bool) : Tot bool = not b

[@@__reduce__]
let ll_state_failure_preserved
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (fail: bool)
: Tot vprop
=
    exists_ (fun (i': (if notp fail then state_i1 else state_i2)) -> // the non-failing state gets frozen in time
      exists_ (fun (h': (if notp fail then state_t1 i' else state_t2 i')) ->
        exists_ (
          (choose_cl cl1 cl2 (notp fail)).ll_state_match #i' h'
    )))

[@@__reduce__]
let ll_state_failure_body
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#i: (state_i1 & state_i2))
  (h: state_t state_t1 state_t2 i)
  (fail: bool)
: Tot vprop
=   (choose_cl cl1 cl2 fail).ll_state_failure 
      #(curry_boole_proj i fail)
      (curry_boole_proj h fail) `star`
    ll_state_failure_preserved cl1 cl2 fail

[@@__reduce__]
let ll_state_failure
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#i: (state_i1 & state_i2))
  (h: state_t state_t1 state_t2 i)
: Tot vprop
= exists_ (fun (fail: bool) ->
    ll_state_failure_body cl1 cl2 h fail
  )

let intro_ll_state_failure
  (#opened: _)
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#i: (state_i1 & state_i2))
  (h: state_t state_t1 state_t2 i)
  (fail: bool)
: STGhostT unit opened
    ((choose_cl cl1 cl2 fail).ll_state_failure 
      #(curry_boole_proj i fail)
      (curry_boole_proj h fail) `star`
      ll_state_failure_preserved cl1 cl2 fail)
    (fun _ -> ll_state_failure cl1 cl2 h)
= noop ()

[@@__reduce__]
let ll_state_pts_to
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (p: (ll_state_ptr1 & ll_state_ptr2))
  (s: (ll_state1 & ll_state2))
: Tot vprop
= cl1.ll_state_pts_to (fstp p) (fstp s) `star`
  cl2.ll_state_pts_to (sndp p) (sndp s)

let state_ge
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#i1: (state_i1 & state_i2)) (s1: state_t state_t1 state_t2 i1)
  (#i2: (state_i1 & state_i2)) (s2: state_t state_t1 state_t2 i2)
: Tot prop
= cl1.state_ge #(fstp i1) (fstp s1) #(fstp i2) (fstp s2) /\
  cl2.state_ge #(sndp i1) (sndp s1) #(sndp i2) (sndp s2)

let ll_state_failure_inc
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#opened: _)
  (#i1: (state_i1 & state_i2)) (s1: state_t state_t1 state_t2 i1)
  (#i2: (state_i1 & state_i2)) (s2: state_t state_t1 state_t2 i2)  
: STGhost unit opened
    (ll_state_failure cl1 cl2 s1)
    (fun _ -> ll_state_failure cl1 cl2 s2)
    (state_ge cl1 cl2 s2 s1)
    (fun _ -> True)
=
      let fail = elim_exists () in
      (choose_cl cl1 cl2 fail).ll_state_failure_inc #_ #(curry_boole_proj i1 fail) (curry_boole_proj s1 fail) #(curry_boole_proj i2 fail) (curry_boole_proj s2 fail);
      noop ()

let cl
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
: Tot (low_level_state (state_i1 & state_i2) (state_t state_t1 state_t2) (ll_state1 & ll_state2) (ll_state_ptr1 & ll_state_ptr2))
= {
    ll_state_match = ll_state_match cl1 cl2;
    ll_state_failure = ll_state_failure cl1 cl2;
    state_ge = state_ge cl1 cl2;
    state_ge_refl = (fun s -> cl1.state_ge_refl (fstp s); cl2.state_ge_refl (sndp s));
    state_ge_trans = (fun s1 s2 s3 -> cl1.state_ge_trans (fstp s1) (fstp s2) (fstp s3); cl2.state_ge_trans (sndp s1) (sndp s2) (sndp s3));
    ll_state_failure_inc = ll_state_failure_inc cl1 cl2;
    ll_state_shape = (fun i l ->
      cl1.ll_state_shape (fstp i) (fstp l) /\
      cl2.ll_state_shape (sndp i) (sndp l)
    );
    ll_state_match_shape = (fun h l ->
      cl1.ll_state_match_shape (fstp h) (fstp l);
      cl2.ll_state_match_shape (sndp h) (sndp l)
    );
    ll_state_pts_to = ll_state_pts_to cl1 cl2
  }

inline_for_extraction
let with_ll_state_ptr
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (#cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (#cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#i1: state_i1)
  (w1: with_ll_state_ptr_t cl1 i1)
  (#i2: state_i2)
  (w2: with_ll_state_ptr_t cl2 i2)
: Tot (with_ll_state_ptr_t (cl cl1 cl2) (i1, i2))
= fun l k ->
    w1 (fstp l) (fun p1 ->
      w2 (sndp l) (fun p2 ->
        rewrite
          (cl1.ll_state_pts_to p1 (fstp l) `star` cl2.ll_state_pts_to p2 (sndp l))
          ((cl cl1 cl2).ll_state_pts_to (p1, p2) l);
        let res = k (p1, p2) in
        let l' = elim_exists () in
        rewrite ((cl cl1 cl2).ll_state_pts_to (p1, p2) l') (ll_state_pts_to cl1 cl2 (p1, p2) l');
        return res        
      )
    )

inline_for_extraction
let load_ll_state_ptr
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (#cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (#cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#i1: state_i1)
  (w1: load_ll_state_ptr_t cl1 i1)
  (#i2: state_i2)
  (w2: load_ll_state_ptr_t cl2 i2)
: Tot (load_ll_state_ptr_t (cl cl1 cl2) (i1, i2))
= fun #gl p k ->
    rewrite
      ((cl cl1 cl2).ll_state_pts_to p gl)
      (ll_state_pts_to cl1 cl2 p gl);
    w1 (fstp p) (fun l1 ->
      w2 (sndp p) (fun l2 ->
        rewrite
          (ll_state_pts_to cl1 cl2 p (l1, l2))
          ((cl cl1 cl2).ll_state_pts_to p (l1, l2));
        k (l1, l2)
      )
    )

inline_for_extraction
let store_ll_state_ptr
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (#cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (#cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#i1: state_i1)
  (w1: store_ll_state_ptr_t cl1 i1)
  (#i2: state_i2)
  (w2: store_ll_state_ptr_t cl2 i2)
: Tot (store_ll_state_ptr_t (cl cl1 cl2) (i1, i2))
= fun #gl p l' ->
    rewrite
      ((cl cl1 cl2).ll_state_pts_to p gl)
      (ll_state_pts_to cl1 cl2 p gl);
    w1 (fstp p) (fstp l');
    w2 (sndp p) (sndp l');
    rewrite
      (ll_state_pts_to cl1 cl2 p l')
      ((cl cl1 cl2).ll_state_pts_to p l')

[@specialize]
let ptr_cl
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (#cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (ptr_cl1: ll_state_ptr_ops cl1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (#cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (ptr_cl2: ll_state_ptr_ops cl2)
= {
    with_ll_state_ptr = (fun inv -> with_ll_state_ptr (ptr_cl1.with_ll_state_ptr (fstp inv)) (ptr_cl2.with_ll_state_ptr (sndp inv)));
    load_ll_state_ptr = (fun inv -> load_ll_state_ptr (ptr_cl1.load_ll_state_ptr (fstp inv)) (ptr_cl2.load_ll_state_ptr (sndp inv)));
    store_ll_state_ptr = (fun inv -> store_ll_state_ptr (ptr_cl1.store_ll_state_ptr (fstp inv)) (ptr_cl2.store_ll_state_ptr (sndp inv)));
  }

[@@specialize]
noeq
type action_t
  (#state_i1: Type)
  (action_t1: (t: Type) -> (pre: state_i1) -> (post: state_i1) -> Type)
  (#state_i2: Type)
  (action_t2: (t: Type) -> (pre: state_i2) -> (post: state_i2) -> Type)
: Type -> (state_i1 & state_i2) -> (state_i1 & state_i2) -> Type
= | A1:
      (#t: Type) ->
      (#pre1: state_i1) ->
      (#post1: state_i1) ->
      (a: action_t1 t pre1 post1) ->
      (frame: state_i2) ->
      action_t action_t1 action_t2 t (pre1, frame) (post1, frame)
  | A2:
      (#t: Type) ->
      (#pre2: state_i2) ->
      (#post2: state_i2) ->
      (a: action_t2 t pre2 post2) ->
      (frame: state_i1) ->
      action_t action_t1 action_t2 t (frame, pre2) (frame, post2)

let a1_sem
  (#state_i1: Type) (state_t1: (state_i1 -> Type))
  (#state_i2: Type) (state_t2: (state_i2 -> Type))
  (#t: Type)
  (#pre1: state_i1)
  (#post1: state_i1)
  (f: stt state_t1 t pre1 post1)
  (frame: state_i2)
: Tot (stt (state_t state_t1 state_t2) t (pre1, frame) (post1, frame))
= fun (s1, s2) ->
    let (v, s1') = f s1 in
    (v, (s1', s2))

let a2_sem
  (#state_i1: Type) (state_t1: (state_i1 -> Type))
  (#state_i2: Type) (state_t2: (state_i2 -> Type))
  (#t: Type)
  (#pre2: state_i2)
  (#post2: state_i2)
  (f: stt state_t2 t pre2 post2)
  (frame: state_i1)
: Tot (stt (state_t state_t1 state_t2) t (frame, pre2) (frame, post2))
= fun (s1, s2) ->
    let (v, s2') = f s2 in
    (v, (s1, s2'))

let action_sem
  (#state_i1: Type)
  (#action_t1: (t: Type) -> (pre: state_i1) -> (post: state_i1) -> Type)
  (#state_t1: (state_i1 -> Type))
  (action_sem1: ((#t: Type) -> (#pre: state_i1) -> (#post: state_i1) -> (a: action_t1 t pre post) -> stt state_t1 t pre post))
  (#state_i2: Type)
  (#action_t2: (t: Type) -> (pre: state_i2) -> (post: state_i2) -> Type)
  (#state_t2: (state_i2 -> Type))
  (action_sem2: ((#t: Type) -> (#pre: state_i2) -> (#post: state_i2) -> (a: action_t2 t pre post) -> stt state_t2 t pre post))
  (#t: Type)
  (#pre #post: (state_i1 & state_i2))
  (a: action_t action_t1 action_t2 t pre post)
: Tot (stt (state_t state_t1 state_t2) t pre post)
= match a with
  | A1 f frame -> a1_sem state_t1 state_t2 (action_sem1 f) frame
  | A2 f frame -> a2_sem state_t1 state_t2 (action_sem2 f) frame

inline_for_extraction
let a1_impl'
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#t: Type)
  (#pre1: state_i1)
  (#post1: state_i1)
  (f: stt state_t1 t pre1 post1)
  (kpre0: vprop)
  (kpost: vprop)
  (fi: (kpre: vprop) -> stt_impl_t' cl1 f (kpre0 `star` kpre) kpost)
  (frame: state_i2)
: Tot (stt_impl_t' (cl cl1 cl2) (a1_sem state_t1 state_t2 f frame) kpre0 kpost)
= fun out h k_success k_failure ->
    rewrite
      ((cl cl1 cl2).ll_state_match h out)
      (ll_state_match cl1 cl2 h out);
    fi
      (cl2.ll_state_match _ _)
      _ _
      (fun out1' h1' v ->
        [@inline_let] // CRITICAL for extraction
        let out' = (out1', sndp out) in
        let h' : Ghost.erased (state_t state_t1 state_t2 (post1, frame)) = Ghost.hide (Ghost.reveal h1', sndp h) in
        rewrite
          (cl1.ll_state_match _ _ `star` cl2.ll_state_match _ _)
          ((cl cl1 cl2).ll_state_match h' out');
        k_success _ _ v)
      (fun h1' v ->
        let h' : Ghost.erased (state_t state_t1 state_t2 (post1, frame)) = Ghost.hide (Ghost.reveal h1', sndp h) in
        rewrite
          (cl1.ll_state_failure h1')
          ((choose_cl cl1 cl2 true).ll_state_failure #(curry_boole_proj (post1, frame) true) (curry_boole_proj h' true));
        rewrite
          (cl2.ll_state_match _ _)
          ((choose_cl cl1 cl2 (notp true)).ll_state_match #frame (sndp h) (sndp out));
        intro_ll_state_failure cl1 cl2 h' true;
        rewrite
          (ll_state_failure cl1 cl2 h')
          ((cl cl1 cl2).ll_state_failure h');
        k_failure _ v
      )

inline_for_extraction
let a1_impl
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#t: Type)
  (#pre1: state_i1)
  (#post1: state_i1)
  (#f: stt state_t1 t pre1 post1)
  (fi: stt_impl_t cl1 f)
  (frame: state_i2)
: Tot (stt_impl_t (cl cl1 cl2) (a1_sem state_t1 state_t2 f frame))
= fun kpre0 kpost -> a1_impl' cl1 cl2 f kpre0 kpost (fun kpre -> fi (kpre0 `star` kpre) kpost) frame

inline_for_extraction
let a2_impl'
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#t: Type)
  (#pre2: state_i2)
  (#post2: state_i2)
  (f: stt state_t2 t pre2 post2)
  (kpre0: vprop)
  (kpost: vprop)
  (fi: (kpre: vprop) -> stt_impl_t' cl2 f (kpre0 `star` kpre) kpost)
  (frame: state_i1)
: Tot (stt_impl_t' (cl cl1 cl2) (a2_sem state_t1 state_t2 f frame) kpre0 kpost)
= fun out h k_success k_failure ->
    rewrite
      ((cl cl1 cl2).ll_state_match h out)
      (ll_state_match cl1 cl2 h out);
    fi
      (cl1.ll_state_match _ _)
      _ _
      (fun out2' h2' v ->
        [@inline_let] // CRITICAL for extraction
        let out' = (fstp out, out2') in
        let h' : Ghost.erased (state_t state_t1 state_t2 (frame, post2)) = Ghost.hide (fstp h, Ghost.reveal h2') in
        rewrite
          (cl1.ll_state_match _ _ `star` cl2.ll_state_match _ _)
          ((cl cl1 cl2).ll_state_match h' out');
        k_success _ _ v)
      (fun h2' v ->
        let h' : Ghost.erased (state_t state_t1 state_t2 (frame, post2)) = Ghost.hide (fstp h, Ghost.reveal h2') in
        rewrite
          (cl2.ll_state_failure h2')
          ((choose_cl cl1 cl2 false).ll_state_failure #(curry_boole_proj (frame, post2) false) (curry_boole_proj h' false));
        rewrite
          (cl1.ll_state_match _ _)
          ((choose_cl cl1 cl2 (notp false)).ll_state_match #frame (fstp h) (fstp out));
        intro_ll_state_failure cl1 cl2 h' false;
        rewrite
          (ll_state_failure cl1 cl2 h')
          ((cl cl1 cl2).ll_state_failure h');
        k_failure _ v
      )

inline_for_extraction
let a2_impl
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#t: Type)
  (#pre2: state_i2)
  (#post2: state_i2)
  (#f: stt state_t2 t pre2 post2)
  (fi: stt_impl_t cl2 f)
  (frame: state_i1)
: Tot (stt_impl_t (cl cl1 cl2) (a2_sem state_t1 state_t2 f frame))
= fun kpre0 kpost -> a2_impl' cl1 cl2 f kpre0 kpost (fun kpre -> fi (kpre0 `star` kpre) kpost) frame

[@@specialize]
let impl_action
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (#cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (#cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#action_t1: (t: Type) -> (pre: state_i1) -> (post: state_i1) -> Type)
  (#action_sem1: ((#t: Type) -> (#pre: state_i1) -> (#post: state_i1) -> (a: action_t1 t pre post) -> stt state_t1 t pre post))
  (action_impl1: ((#rt: Type) -> (#pre: _) -> (#post: _) -> (a: action_t1 rt pre post) -> stt_impl_t (cl1) (action_sem1 a)))
  (#action_t2: (t: Type) -> (pre: state_i2) -> (post: state_i2) -> Type)
  (#action_sem2: ((#t: Type) -> (#pre: state_i2) -> (#post: state_i2) -> (a: action_t2 t pre post) -> stt state_t2 t pre post))
  (action_impl2: ((#rt: Type) -> (#pre: _) -> (#post: _) -> (a: action_t2 rt pre post) -> stt_impl_t (cl2) (action_sem2 a)))
  (#t: Type)
  (#pre #post: (state_i1 & state_i2))
  (a: action_t action_t1 action_t2 t pre post)
: Tot (stt_impl_t (cl cl1 cl2) (action_sem action_sem1 action_sem2 a))
= match a with
  | A1 a frame -> LowParse.Spec.Base.coerce _ (a1_impl cl1 cl2 (action_impl1 a) frame)
  | A2 a frame -> LowParse.Spec.Base.coerce _ (a2_impl cl1 cl2 (action_impl2 a) frame)

[@@specialize]
let a_cl
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (#cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#action_t1: (t: Type) -> (pre: state_i1) -> (post: state_i1) -> Type)
  (#action_sem1: ((#t: Type) -> (#pre: state_i1) -> (#post: state_i1) -> (a: action_t1 t pre post) -> stt state_t1 t pre post))
  (a_cl1: action_impl cl1 action_t1 action_sem1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (#cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#action_t2: (t: Type) -> (pre: state_i2) -> (post: state_i2) -> Type)
  (#action_sem2: ((#t: Type) -> (#pre: state_i2) -> (#post: state_i2) -> (a: action_t2 t pre post) -> stt state_t2 t pre post))
  (a_cl2: action_impl cl2 action_t2 action_sem2)
: Tot (action_impl (cl cl1 cl2) (action_t action_t1 action_t2) (action_sem action_sem1 action_sem2))
= {
    a_inc = (fun #t #pre #post (a: action_t action_t1 action_t2 t pre post) (h: state_t state_t1 state_t2 pre) ->
      match a with
      | A1 a _ -> a_cl1.a_inc a (fstp h); cl2.state_ge_refl (sndp h)
      | A2 a _ -> a_cl2.a_inc a (sndp h); cl1.state_ge_refl (fstp h)
    );
    a_impl = impl_action a_cl1.a_impl a_cl2.a_impl
  }

inline_for_extraction
let mk_ll_state
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (#cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (#cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (#vpre1: vprop)
  (#i1: state_i1)
  (#h1: state_t1 i1)
  (mk1: mk_ll_state_t cl1 vpre1 h1)
  (#vpre2: vprop)
  (#i2: state_i2)
  (#h2: state_t2 i2)
  (mk2: mk_ll_state_t cl2 vpre2 h2)
: Tot (mk_ll_state_t (cl cl1 cl2) (vpre1 `star` vpre2) #(i1, i2) (h1, h2))
= fun k ->
    mk1 (fun out1 ->
    mk2 (fun out2 ->
      rewrite
        (cl1.ll_state_match _ _ `star` cl2.ll_state_match _ _)
        ((cl cl1 cl2).ll_state_match (h1, h2) (out1, out2));
      k _
    ))

let choose_no_fail
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (#cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (no_fail1: no_ll_state_failure_t cl1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (#cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (no_fail2: no_ll_state_failure_t cl2)
  (b: bool)
: Tot (no_ll_state_failure_t (choose_cl cl1 cl2 b))
= if b
  then coerce _ no_fail1
  else coerce _ no_fail2

let no_fail
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (#cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (no_fail1: no_ll_state_failure_t cl1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (#cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (no_fail2: no_ll_state_failure_t cl2)
: Tot (no_ll_state_failure_t (cl cl1 cl2))
= fun #i h ->
  rewrite
    ((cl cl1 cl2).ll_state_failure h)
    (ll_state_failure cl1 cl2 h);
  let fail = elim_exists () in
  choose_no_fail no_fail1 no_fail2 _ _;
  rewrite // by contradiction
    (ll_state_failure_preserved cl1 cl2 fail)
    emp

let ll_state_failure_elim_no_fail
  (#opened: _)
  (#state_i1: Type) (#state_t1: state_i1 -> Type) (#ll_state1: Type) (#ll_state_ptr1: Type)
  (cl1: low_level_state state_i1 state_t1 ll_state1 ll_state_ptr1)
  (#state_i2: Type) (#state_t2: state_i2 -> Type) (#ll_state2: Type) (#ll_state_ptr2: Type)
  (cl2: low_level_state state_i2 state_t2 ll_state2 ll_state_ptr2)
  (b: bool)
  (no_fail: no_ll_state_failure_t (choose_cl cl1 cl2 b))
  (#i: _)
  (h: state_t state_t1 state_t2 i)
: STGhostT unit opened
    ((cl cl1 cl2).ll_state_failure h)
    (fun _ -> ll_state_failure_body cl1 cl2 h (notp b))
=
  rewrite
    ((cl cl1 cl2).ll_state_failure h)
    (ll_state_failure cl1 cl2 h);
  let fail = elim_exists () in
  if Ghost.reveal fail = b
  then begin
    coerce (no_ll_state_failure_t (choose_cl cl1 cl2 fail)) no_fail _;
    rewrite // by contradiction
      (ll_state_failure_preserved cl1 cl2 fail)
      (ll_state_failure_body cl1 cl2 h (notp b))
  end else begin
    rewrite
      (ll_state_failure_body cl1 cl2 h fail)
      (ll_state_failure_body cl1 cl2 h (notp b))
  end
