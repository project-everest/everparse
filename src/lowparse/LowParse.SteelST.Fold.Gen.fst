module LowParse.SteelST.Fold.Gen
include LowParse.Spec.Fold

#set-options "--ide_id_info_off"

open Steel.ST.GenElim
open LowParse.SteelST.Combinators
open LowParse.SteelST.List
open LowParse.SteelST.Int
open LowParse.SteelST.VLData

module AP = LowParse.SteelST.ArrayPtr
module LP = LowParse.Spec.Base
module SZ = LowParse.Steel.StdInt

let pkind = {
  parser_kind_low = 1;
  parser_kind_high = None;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let parse_bool : parser (parse_filter_kind parse_u8_kind) bool =
  parse_u8
    `parse_filter`
    (fun x -> (x = 1uy || x = 0uy))
    `parse_synth`
    (fun x -> (x = 1uy))

let serialize_bool : serializer parse_bool =
  serialize_synth
    (parse_u8 `parse_filter` (fun x -> (x = 1uy || x = 0uy)))
    (fun x -> (x = 1uy))
    (serialize_u8 `serialize_filter` (fun x -> (x = 1uy || x = 0uy)))
    (fun y -> if y then 1uy else 0uy)
    ()

inline_for_extraction
let read_bool : leaf_reader parse_bool =
  read_synth'
    (read_filter read_u8 (fun x -> (x = 1uy || x = 0uy)))
    (fun x -> (x = 1uy))
    ()

inline_for_extraction
noeq
type low_level_state
  (state_i: Type) (state_t: state_i -> Type) (ll_state: Type) (ll_state_ptr: Type)
= {
    ll_state_match: ((#i: state_i) -> (h: state_t i) -> ll_state -> vprop);
    ll_state_failure: ((#i: state_i) -> (h: state_t i) -> vprop);
    state_ge: ((#i1: state_i) -> (s1: state_t i1) -> (#i2: state_i) -> (s2: state_t i2) -> prop);
    state_ge_refl: (
      (#i: state_i) -> (s: state_t i) ->
      Lemma
      (state_ge s s)
    );
    state_ge_trans: (
      (#i1: state_i) -> (s1: state_t i1) ->
      (#i2: state_i) -> (s2: state_t i2) ->
      (#i3: state_i) -> (s3: state_t i3) ->
      Lemma
      (requires (
        state_ge s1 s2 /\
        state_ge s2 s3
      ))
      (ensures (state_ge s1 s3))
    );
    ll_state_failure_inc: (
      (#opened: _) ->
      (#i1: state_i) -> (s1: state_t i1) ->
      (#i2: state_i) -> (s2: state_t i2) ->
      STGhost unit opened
        (ll_state_failure s1)
        (fun _ -> ll_state_failure s2)
        (state_ge s2 s1)
        (fun _ -> True)
    );
    ll_state_shape: (state_i -> ll_state -> prop);
    ll_state_match_shape: (
      (#opened: _) ->
      (#i: state_i) ->
      (h: state_t i) ->
      (l: ll_state) ->
      STGhost unit opened
        (ll_state_match h l)
        (fun _ -> ll_state_match h l)
        True
        (fun _ -> ll_state_shape i l)
    );
    ll_state_pts_to: (ll_state_ptr -> ll_state -> vprop);
  }

inline_for_extraction
let with_ll_state_ptr_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (i: state_i)
: Tot Type
=
  (l: ll_state) ->
  (#kpre: vprop) ->
  (#t: Type) ->
  (#kpost: (t -> vprop)) ->
  (k: (
    (p: ll_state_ptr) ->
    STT t
      (kpre `star` cl.ll_state_pts_to p l)
      (fun r -> kpost r `star` exists_ (cl.ll_state_pts_to p))
  )) ->
  STF t kpre kpost (cl.ll_state_shape i l) (fun _ -> True)

inline_for_extraction
let load_ll_state_ptr_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (i: state_i)
: Tot Type
=
  (#gl: Ghost.erased ll_state) ->
  (p: ll_state_ptr) ->
  (#kpre: vprop) ->
  (#t: Type) ->
  (#kpost: (t -> vprop)) ->
  (k: (
    (l: ll_state) ->
    ST t
       (kpre `star` cl.ll_state_pts_to p l)
       kpost
       (l == Ghost.reveal gl)
       (fun _ -> True)
  )) ->
  STF t
    (kpre `star` cl.ll_state_pts_to p gl)
    kpost
    (cl.ll_state_shape i gl)
    (fun _ -> True)

inline_for_extraction
let store_ll_state_ptr_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (i: state_i)
: Tot Type
= (#gl: Ghost.erased ll_state) ->
  (p: ll_state_ptr) ->
  (l': ll_state) ->
  ST unit
     (cl.ll_state_pts_to p gl)
     (fun _ -> cl.ll_state_pts_to p l')
     (cl.ll_state_shape i gl /\ cl.ll_state_shape i l')
     (fun _ -> True)

inline_for_extraction
[@@noextract_to "krml"]
let stt_impl_t'
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
  (kpre: vprop)
  (kpost: vprop)
: Tot Type
= (bout: ll_state) ->
  (h: Ghost.erased (state_t pre)) ->
  (k_success: (
    (bout': ll_state) ->
    (h': Ghost.erased (state_t post)) ->
    (v: ret_t) ->
    ST unit
      (kpre `star`
        cl.ll_state_match h' bout')
      (fun _ -> kpost)
      (
        p h == (v, Ghost.reveal h')
      )
      (fun _ -> True)
  )) ->
  (k_failure: (
    (h': Ghost.erased (state_t post)) ->
    (v: Ghost.erased ret_t) ->
    ST unit
      (kpre `star` cl.ll_state_failure h')
      (fun _ -> kpost)
      (
        p h == (Ghost.reveal v, Ghost.reveal h')
      )
      (fun _ -> True)
  )) ->
  STT unit
    (kpre `star`
      cl.ll_state_match h bout)
    (fun _ -> kpost)

inline_for_extraction
[@@noextract_to "krml"]
let stt_impl_t
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
: Tot Type
=
  (kpre: vprop) ->
  (kpost: vprop) ->
  stt_impl_t' cl p kpre kpost

inline_for_extraction
[@@noextract_to "krml"]
let fold_impl_t
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ty: Type)
  (#kty: parser_kind)
  (pty: parser kty ty)
  (p: fold_t state_t ty ret_t pre post)
: Tot Type
=
  (kpre: vprop) ->
  (kpost: vprop) ->
  (#vbin: v kty ty) ->
  (bin: byte_array) ->
  stt_impl_t' cl (p vbin.contents)
    (kpre `star` aparse pty bin vbin)
    kpost

inline_for_extraction
let impl_action
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: Ghost.erased (stt state_t ret_t pre post))
  (pi: stt_impl_t cl p)
  (#ty: Type)
  (#kty: parser_kind)
  (pty: parser kty ty)
: Tot (fold_impl_t cl pty (action_fold p))
= fun kpre kpost (#vbin: v kty ty) (bin: byte_array) ->
    pi (kpre `star` aparse pty bin vbin) kpost

inline_for_extraction
[@@noextract_to "krml"]
let impl_ret
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (i: state_i)
  (v: ret_t)
: Tot (stt_impl_t cl (ret #state_i #state_t #i v))
= fun kpre kpost bout h k_success k_failure ->
    k_success bout h v

inline_for_extraction
let impl_rewrite_parser
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ty: Type)
  (p: Ghost.erased (fold_t state_t ty ret_t pre post))
  (#kty: parser_kind)
  (#pty: parser kty ty)
  (pi: fold_impl_t cl pty p)
  (#kty': parser_kind)
  (pty': parser kty' ty)
: Pure (fold_impl_t cl pty' p)
    (requires (forall x . parse pty' x == parse pty x))
    (ensures (fun _ -> True))
= fun kpre kpost (#vbin': v kty' ty) (bin: byte_array) bout h k_success k_failure ->
    let vbin : v kty ty = rewrite_aparse bin pty in
    let restore (#opened: _) () : STGhostT unit opened
      (aparse pty bin vbin)
      (fun _ -> aparse pty' bin vbin')
    = let _ = rewrite_aparse bin pty' in
      vpattern_rewrite (aparse pty' bin) vbin'
    in
    pi
      kpre kpost #vbin bin bout h
      (fun bout1 h1 v1 ->
        restore ();
        k_success bout1 h1 v1
      )
      (fun h1 v1 ->
        restore ();
        k_failure h1 v1)

inline_for_extraction
[@@noextract_to "krml"]
let impl_read
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (i: state_i)
  (#ty: Type)
  (#kty: parser_kind)
  (#pty: parser kty ty)
  (rty: leaf_reader pty)
: Tot (fold_impl_t cl pty (fold_read #state_i #state_t #i #ty ()))
= fun kpre kpost (#vbin: v kty ty) (bin: byte_array) bout h k_success k_failure ->
    let v = rty bin in
    k_success bout h v

let stt_state_inc
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
: Tot Type
= (s: state_t pre) ->
  Lemma
  (snd (p s) `cl.state_ge` s)

let fold_state_inc
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ty: Type)
  (p: fold_t state_t ty ret_t pre post)
: Tot Type
= (i: ty) ->
  stt_state_inc cl (p i)

let get_return_state
  #state_i #state_t
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
  (s: state_t pre)
: Pure (Ghost.erased (state_t post))
    (requires True)
    (ensures (fun y -> Ghost.reveal y == sndp (p s)))
= sndp (p s)

let get_return_value
  #state_i #state_t
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
  (s: state_t pre)
: Pure (Ghost.erased ret_t)
    (requires True)
    (ensures (fun y -> Ghost.reveal y == fstp (p s)))
= fstp (p s)

[@@noextract_to "krml"]
inline_for_extraction
let impl_bind
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#ty: Type)
  (#kty: parser_kind)
  (pty: parser kty ty)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (#ret2: _)
  (#post2: _)
  (f: Ghost.erased (fold_t state_t ty ret1 pre1 post1))
  (impl_f: fold_impl_t cl pty f)
  (g: Ghost.erased ((x: ret1) -> fold_t state_t ty ret2 post1 post2))
  (impl_g: ((x: ret1) -> fold_impl_t cl pty (Ghost.reveal g x)))
  (g_prf: ((x: ret1) -> fold_state_inc cl (Ghost.reveal g x)))
: Tot (fold_impl_t cl pty (bind_fold f g))
= fun kpre kpost (#vbin: v kty ty) (bin: byte_array) bout h k_success k_failure ->
    impl_f
      kpre kpost bin bout h
      (fun bout1 h1 v1 ->
        impl_g v1
          kpre kpost bin bout1 h1 k_success k_failure
      )
      (fun h1 v1 ->
        let h2 = get_return_state (Ghost.reveal g v1 vbin.contents) h1 in
        let v2 = get_return_value (Ghost.reveal g v1 vbin.contents) h1 in
        g_prf v1 vbin.contents h1;
        cl.ll_state_failure_inc h1 h2;
        k_failure h2 v2
      )

inline_for_extraction
[@@noextract_to "krml"]
let impl_if
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#t: Type)
  (#ret: Type)
  (#pre: _)
  (#post: _)
  (x: bool)
  (f1: Ghost.erased (squash (x == true) -> fold_t state_t t ret pre post))
  (#k: parser_kind)
  (p: parser k t)
  (impl_f1: squash (x == true) -> fold_impl_t cl p (Ghost.reveal f1 ()))
  (f2: Ghost.erased (squash (x == false) -> fold_t state_t t ret pre post))
  (impl_f2: squash (x == false) -> fold_impl_t cl p (Ghost.reveal f2 ()))
: Tot (fold_impl_t cl p (if x then Ghost.reveal f1 () else Ghost.reveal f2 ()))
= fun kpre kpost #vbin bin bout h k_success k_failure ->
    if x
    then impl_f1 () kpre kpost bin bout h k_success k_failure
    else impl_f2 () kpre kpost bin bout h k_success k_failure

inline_for_extraction
[@@noextract_to "krml"]
let impl_pair
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#t1: Type)
  (#t2: Type)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (f1: Ghost.erased (fold_t state_t t1 ret1 pre1 post1))
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (impl_f1: fold_impl_t cl p1 f1)
  (j1: jumper p1) // MUST be computed OUTSIDE of impl_pair
  (#ret2: _)
  (#post2: _)
  (f2: Ghost.erased ((x: ret1) -> fold_t state_t t2 ret2 post1 post2))
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (impl_f2: ((x: ret1) -> fold_impl_t cl p2 (Ghost.reveal f2 x)))
  (f2_prf: ((x: ret1) -> fold_state_inc cl (Ghost.reveal f2 x))) 
: Pure (fold_impl_t cl (p1 `nondep_then` p2) (fold_pair f1 f2))
    (requires (k1.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun kpre kpost #vbin bin bout h k_success k_failure ->
  let bin2 = split_pair j1 p2 bin in
  let _ = gen_elim () in
  let vbin1 = vpattern_replace (aparse p1 bin) in
  let vbin2 = vpattern_replace (aparse p2 bin2) in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse p1 bin vbin1 `star` aparse p2 bin2 vbin2)
    (fun _ -> aparse (p1 `nondep_then` p2) bin vbin)
  =
    let _ = merge_pair p1 p2 bin bin2 in
    rewrite (aparse _ bin _) (aparse (p1 `nondep_then` p2) bin vbin)
  in
  impl_f1
    (kpre `star` aparse p2 bin2 vbin2) kpost
    bin bout h
    (fun bout1 h1 v1 ->
      impl_f2 v1
        (kpre `star` aparse p1 bin vbin1) kpost
        bin2 bout1 h1
        (fun bout2 h2 v2 ->
          restore ();
          k_success bout2 h2 v2
        )
        (fun h2 v2 ->
          restore ();
          k_failure h2 v2
        )
    )
    (fun h1 v1 ->
      let h2 = get_return_state (Ghost.reveal f2 v1 vbin2.contents) h1 in
      let v2 = get_return_value (Ghost.reveal f2 v1 vbin2.contents) h1 in
      f2_prf v1 vbin2.contents h1;
      cl.ll_state_failure_inc h1 h2;
      restore ();
      k_failure h2 v2
    )

let parser_of_choice_payload
  (#k: parser_kind)
  (t: (bool -> Type))
  (f: (x: bool) -> parser k (t x))
  (x: bool)
: Tot (parser k (t x))
= f x

inline_for_extraction
[@@noextract_to "krml"]
let impl_choice
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#t: (bool -> Type))
  (#ret_t: Type)
  (#pre: _)
  (#post: _)
  (f: Ghost.erased ((x: bool) -> fold_t state_t (t x) ret_t pre post))
  (#k: parser_kind)
  (p: (x: bool) -> parser k (t x))
  (impl_f: (x: bool) -> fold_impl_t cl (p x) (Ghost.reveal f x))
: Tot (fold_impl_t cl (parse_dtuple2 parse_bool p) (fold_choice f))
= fun kpre kpost #vbin bin bout h k_success k_failure ->
  let bin_pl = split_dtuple2
    (jump_constant_size parse_bool (SZ.mk_size_t 1ul))
    p
    bin
  in
  let tag = read_dtuple2_tag read_bool p bin bin_pl in
  let _ = gen_elim () in
  let vbin_tag = vpattern_replace (aparse parse_bool bin) in
  let vbin_pl = vpattern_replace (aparse (p tag) bin_pl) in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse parse_bool bin vbin_tag `star` aparse (p tag) bin_pl vbin_pl)
    (fun _ -> aparse (parse_dtuple2 parse_bool p) bin vbin)
  =
    let _ = intro_dtuple2 parse_bool p bin bin_pl in
    rewrite (aparse _ bin _) (aparse (parse_dtuple2 parse_bool p) bin vbin)
  in
  impl_f tag
    (kpre `star` aparse parse_bool bin vbin_tag) kpost
    bin_pl bout h
    (fun bout' h' v' ->
      restore ();
      k_success bout' h' v'
    )
    (fun h' v' ->
      restore ();
      k_failure h' v'
    )

module R = Steel.ST.Reference

(* for loop *)

unfold
let impl_for_inv_true_prop0
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (from: SZ.size_t)
  (h: state_t inv)
  (cont: bool)
: Tot prop
=
  SZ.size_v from0 <= SZ.size_v from /\
  fold_for inv (SZ.size_v from0) (SZ.size_v (if SZ.size_v from <= SZ.size_v to then from else to)) f l h0 == ((), h) /\
  (cont == (SZ.size_v from < SZ.size_v to))

let impl_for_inv_true_prop
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (from: SZ.size_t)
  (h: state_t inv)
  (cont: bool)
: Tot prop
= impl_for_inv_true_prop0 inv from0 to f l h0 from h cont

[@@__reduce__]
let impl_for_inv_aux_true
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (out: ll_state)
  (from: SZ.size_t)
  (cont: bool)
: Tot vprop
= exists_ (fun (h: state_t inv) ->
    cl.ll_state_match h out `star`
    pure (
      impl_for_inv_true_prop inv from0 to f l h0 from h cont
    )
  )

let fold_for_loop_body
  #state_i (state_t: _)
  (inv: state_i)
  (t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
: Tot Type
= Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv)

let impl_for_inv_aux_false_prop
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (h: state_t inv)
  (cont: bool)
  (from: SZ.size_t)
: Tot prop
=
    SZ.size_v from0 <= SZ.size_v from /\ SZ.size_v from <= SZ.size_v to /\
    fold_for inv (SZ.size_v from0) (SZ.size_v from) f l h0 == ((), h) /\
    cont == false

[@@__reduce__]
let impl_for_inv_aux_false0
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (cont: bool)
  (from: SZ.size_t)
: Tot vprop
=
  exists_ (fun h ->
    cl.ll_state_failure h `star`
    pure (impl_for_inv_aux_false_prop inv from0 to f l h0 h cont from)
  )

let impl_for_inv_aux_false
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (cont: bool)
: (from: SZ.size_t) ->
  Tot vprop
=
  impl_for_inv_aux_false0 cl inv from0 to f l h0 cont

let intro_impl_for_inv_aux_false
  (#opened: _)
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (cont: bool)
  (from: SZ.size_t)
  (h: state_t inv)
: STGhost unit opened
    (cl.ll_state_failure h)
    (fun _ -> impl_for_inv_aux_false cl inv from0 to f l h0 cont from)
    (impl_for_inv_aux_false_prop inv from0 to f l h0 h cont from)
    (fun _ -> True)
= noop ();
  rewrite
    (impl_for_inv_aux_false0 cl inv from0 to f l h0 cont from)
    (impl_for_inv_aux_false cl inv from0 to f l h0 cont from)

let impl_for_inv_aux
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (out: ll_state)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: Tot vprop
= if no_interrupt
  then impl_for_inv_aux_true cl inv from0 to f l h0 out from cont
  else exists_ (impl_for_inv_aux_false cl inv from0 to f l h0 cont)

let intro_impl_for_inv_aux_true
  #state_i #state_t #ll_state #ll_state_ptr
  (#opened: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (out: ll_state)
  (from: SZ.size_t)
  (cont: bool)
  (h: state_t inv)
: STGhost unit opened
    (cl.ll_state_match h out)
    (fun _ -> impl_for_inv_aux cl inv from0 to f l h0 out from true cont)
    (impl_for_inv_true_prop inv from0 to f l h0 from h cont)
    (fun _ -> True)
= intro_pure (
    impl_for_inv_true_prop inv from0 to f l h0 from h cont
  );
  rewrite
    (impl_for_inv_aux_true cl inv from0 to f l h0 out from cont)
    (impl_for_inv_aux cl inv from0 to f l h0 out from true cont)

let elim_impl_for_inv_aux_true
  #opened
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (out: ll_state)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: STGhost (Ghost.erased (state_t inv)) opened
    (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (fun h -> cl.ll_state_match h out)
    (no_interrupt == true)
    (fun h -> impl_for_inv_true_prop inv from0 to f l h0 from h cont)
=
  rewrite
    (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (impl_for_inv_aux_true cl inv from0 to f l h0 out from cont);
  let gh = elim_exists () in
  let _ = gen_elim () in
  gh

let elim_impl_for_inv_aux_false
  #opened
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (out: ll_state)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: STGhost (Ghost.erased (SZ.size_t & state_t inv)) opened
    (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (fun r -> cl.ll_state_failure (sndp r))
    (no_interrupt == false)
    (fun r ->
      impl_for_inv_aux_false_prop inv from0 to f l h0 (sndp r) cont (fstp r)
    )
=
  rewrite
    (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (exists_ (impl_for_inv_aux_false0 cl inv from0 to f l h0 cont));
  let from' = elim_exists () in
  let _ = gen_elim () in
  let h = vpattern (fun h -> cl.ll_state_failure h) in
  let r = Ghost.hide (Ghost.reveal from', h) in
  rewrite (cl.ll_state_failure _) (cl.ll_state_failure (sndp r));
  r

let impl_for_inv_aux_cont_true
  (#opened: _)
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (out: ll_state)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: STGhost unit opened
    (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (fun _ -> impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (cont == true)
    (fun h -> no_interrupt == true)
= if no_interrupt
  then noop ()
  else begin
    let _ = elim_impl_for_inv_aux_false _ _ _ _ _ _ _ _ _ _ _ in
    rewrite // by contradiction
      (cl.ll_state_failure _)
      (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
  end

[@@__reduce__]
let impl_for_inv0
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (bin: byte_array)
  (vl: v k t)
  (bh: ll_state_ptr)
  (h0: state_t inv)
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (cont: bool)
: Tot vprop
= exists_ (fun out -> exists_ (fun from -> exists_ (fun no_interrupt ->
    aparse p bin vl `star`
    cl.ll_state_pts_to bh out `star`
    R.pts_to bfrom full_perm from `star`
    R.pts_to b_no_interrupt full_perm no_interrupt `star`
    R.pts_to bcont full_perm cont `star`
    impl_for_inv_aux cl inv from0 to f vl.contents h0 out from no_interrupt cont
  )))

let impl_for_inv
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (bin: byte_array)
  (vl: v k t)
  (bh: ll_state_ptr)
  (h0: state_t inv)
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (cont: bool)
: Tot vprop
= impl_for_inv0 cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont cont

inline_for_extraction
let impl_for_test
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (bin: byte_array)
  (vl: v k t)
  (bh: ll_state_ptr)
  (h0: Ghost.erased (state_t inv))
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (_: unit)
: STT bool
    (exists_ (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont))
    (fun cont -> impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont cont)
= let gcont = elim_exists () in
  rewrite
    (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont gcont)
    (impl_for_inv0 cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont gcont);
  let _ = gen_elim () in
  let cont = R.read bcont in
  rewrite
    (impl_for_inv0 cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont gcont)
    (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont cont);
  return cont

let rec fold_for_snoc
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (from0 to: nat)
  (f: (x: nat { from0 <= x /\ x < to }) -> fold_t state_t t unit inv inv)
  (from: nat)
  (i: t)
  (s: state_t inv)
: Lemma
  (requires (from0 <= from /\ from < to))
  (ensures (
    let (_, s1) = fold_for inv from0 from f i s in
    fold_for inv from0 (from + 1) f i s == Ghost.reveal f (from) i s1
  ))
  (decreases (from - from0))
= if from = from0
  then ()
  else
    let (_, s1) = Ghost.reveal f from0 i s in
    fold_for_snoc inv (from0 + 1) to f from i s1

inline_for_extraction
let impl_for_body
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (bin: byte_array)
  (vl: v k t)
  (bh: ll_state_ptr)
  (h0: Ghost.erased (state_t inv))
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (fi: (x: SZ.size_t { SZ.size_v from0 <= SZ.size_v x /\ SZ.size_v x < SZ.size_v to }) -> fold_impl_t cl p (Ghost.reveal f (SZ.size_v x)))
  (wl: load_ll_state_ptr_t cl inv)
  (ws: store_ll_state_ptr_t cl inv)
  (_: unit)
: STT unit
    (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont true)
    (fun _ -> exists_ (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont))
=
  rewrite
    (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont true)
    (impl_for_inv0 cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont true);
  let _ = gen_elim () in
  impl_for_inv_aux_cont_true cl inv from0 to f vl.contents h0 _ _ _ _;
  vpattern_rewrite (R.pts_to b_no_interrupt full_perm) true;
  let _ = elim_impl_for_inv_aux_true cl inv from0 to f vl.contents h0 _ _ _ _ in
  cl.ll_state_match_shape _ _;
  let from1 = read_replace bfrom in
  let from2 = SZ.size_add from1 SZ.one_size in
  fold_for_snoc inv (SZ.size_v from0) (SZ.size_v to) f (SZ.size_v from1) vl.contents h0;
  wl bh (fun out1 ->
    vpattern_rewrite (cl.ll_state_match _) out1;
    fi from1
      (
        R.pts_to b_no_interrupt full_perm true `star`
        R.pts_to bcont full_perm true `star`
        R.pts_to bfrom full_perm from1 `star`
        cl.ll_state_pts_to bh out1
      )
      (exists_ (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont))
      bin out1 _
      (fun out2 h2 _ ->
        R.write bfrom from2;
        cl.ll_state_match_shape _ _;
        ws bh out2;
        let cont2 = from2 `SZ.size_lt` to in
        R.write bcont cont2;
        intro_impl_for_inv_aux_true cl inv from0 to f vl.contents h0 out2 from2 cont2 h2;
        rewrite
          (impl_for_inv0 cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont cont2)
          (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont cont2);
        noop ()
      )
      (fun h2 _ ->
        R.write b_no_interrupt false;
        R.write bcont false;
        intro_impl_for_inv_aux_false cl inv from0 to f vl.contents h0 false from2 h2;
        rewrite
          (exists_ (impl_for_inv_aux_false cl inv from0 to f vl.contents h0 false))
          (impl_for_inv_aux cl inv from0 to f vl.contents h0 out1 from1 false false);
        rewrite
          (impl_for_inv0 cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont false)
          (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont false);
        noop ()
      )
  )

let rec fold_for_inc_aux
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: nat) (to: nat)
  (f: ((x: nat { from0 <= x /\ x < to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (from: nat)
  (prf: (x: nat { from0 <= x /\ x < to }) -> fold_state_inc cl (f x))
: Lemma
  (requires (
    from0 <= from /\ from <= to
  ))
  (ensures (
    sndp (fold_for inv from0 to f l h0) `cl.state_ge`
    sndp (fold_for inv from0 from f l h0)
  ))
  (decreases (to - from))
= 
  let (_, h1) = fold_for inv from0 from f l h0 in
  if to = from
  then cl.state_ge_refl h1
  else begin
    fold_for_snoc inv from0 to f from l h0;
    prf from l h1;
    let from' = from + 1 in
    fold_for_inc_aux cl inv from0 to f l h0 from' prf;
    let (_, h2) = fold_for inv from0 from' f l h0 in
    let (_, h3) = fold_for inv from0 to f l h0 in
    cl.state_ge_trans h3 h2 h1
  end

let fold_for_inc
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: nat) (to: nat)
  (f: ((x: nat { from0 <= x /\ x < to }) -> fold_t state_t t unit inv inv))
  (prf: (x: nat { from0 <= x /\ x < to }) -> fold_state_inc cl (f x))
: Tot (fold_state_inc cl (fold_for inv from0 to f))
= fun i h ->
  if from0 > to
  then cl.state_ge_refl h
  else fold_for_inc_aux cl inv from0 to f i h from0 prf

let elim_impl_for_inv_aux_false_strong
  (#opened: _)
  (#state_i: _) (#state_t: _) (#ll_state: _) (#ll_state_ptr: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (prf: (x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_state_inc cl (Ghost.reveal f x))
  (l: t)
  (h0: state_t inv)
  (out: ll_state)
  (from: SZ.size_t)
  (no_interrupt: bool)
  (cont: bool)
: STGhost (Ghost.erased (state_t inv)) opened
    (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (fun r -> cl.ll_state_failure r)
    (no_interrupt == false)
    (fun r ->
      Ghost.reveal r == sndp (fold_for inv (SZ.size_v from0) (SZ.size_v to) f l h0)
    )
= let r0 = elim_impl_for_inv_aux_false _ _ _ _ _ _ _ _ _ _ _ in
  fold_for_inc_aux cl inv (SZ.size_v from0) (SZ.size_v to) f l h0 (SZ.size_v (fstp r0)) prf;
  let res = get_return_state (fold_for inv (SZ.size_v from0) (SZ.size_v to) f l) h0 in
  cl.ll_state_failure_inc (sndp r0) res;
  res

inline_for_extraction
let impl_for_post
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (bin: byte_array)
  (vl: v k t)
  (bh: ll_state_ptr)
  (h0: Ghost.erased (state_t inv))
  (bfrom: R.ref SZ.size_t)
  (b_no_interrupt: R.ref bool)
  (bcont: R.ref bool)
  (kpre kpost: vprop)
  (k_success: (
    (bout': ll_state) ->
    (h': Ghost.erased (state_t inv)) ->
    (v: unit) ->
    ST unit
      (kpre `star`
        aparse p bin vl `star`
        cl.ll_state_match h' bout')
      (fun _ -> kpost)
      (
        fold_for inv (SZ.size_v from0) (SZ.size_v to) f vl.contents h0 == (v, Ghost.reveal h')
      )
      (fun _ -> True)
  ))
  (k_failure: (
    (h': Ghost.erased (state_t inv)) ->
    (v: Ghost.erased unit) ->
    ST unit
      (kpre `star`
        aparse p bin vl `star`
        cl.ll_state_failure h')
      (fun _ -> kpost)
      (
        fold_for inv (SZ.size_v from0) (SZ.size_v to) f vl.contents h0 == (Ghost.reveal v, Ghost.reveal h')
      )
      (fun _ -> True)
  ))
  (prf: (x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_state_inc cl (Ghost.reveal f x))
  (wl: load_ll_state_ptr_t cl inv)
: STT unit
    (kpre `star` impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont false)
    (fun _ -> kpost `star`
      exists_ (cl.ll_state_pts_to bh) `star`
      exists_ (R.pts_to bfrom full_perm) `star`
      exists_ (R.pts_to b_no_interrupt full_perm) `star`
      exists_ (R.pts_to bcont full_perm)
    )
=
    rewrite
      (impl_for_inv cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont false)
      (impl_for_inv0 cl inv p from0 to f bin vl bh h0 bfrom b_no_interrupt bcont false);
    let _ = gen_elim () in
    let no_interrupt = read_replace b_no_interrupt in
    if no_interrupt
    then begin
      let h' = elim_impl_for_inv_aux_true  cl inv from0 to f vl.contents _ _ _ _ _ in
      cl.ll_state_match_shape _ _;
      wl bh (fun out' ->
        vpattern_rewrite (cl.ll_state_match _) out';
        k_success out' h' ()
      )
    end else begin
      let r = elim_impl_for_inv_aux_false_strong cl inv from0 to f prf vl.contents _ _ _ _ _ in
      k_failure r ()
    end

inline_for_extraction
let impl_for
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (from: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (prf: (x: nat { SZ.size_v from <= x /\ x < SZ.size_v to }) -> fold_state_inc cl (Ghost.reveal f x))
  (fi: (x: SZ.size_t { SZ.size_v from <= SZ.size_v x /\ SZ.size_v x < SZ.size_v to }) -> fold_impl_t cl p (Ghost.reveal f (SZ.size_v x)))
  (wc: with_ll_state_ptr_t cl inv) // same
  (wl: load_ll_state_ptr_t cl inv)
  (ws: store_ll_state_ptr_t cl inv)
: Tot (fold_impl_t cl p (fold_for inv (SZ.size_v from) (SZ.size_v to) f))
= fun kpre kpost #vbin bin bout h k_success k_failure ->
  cl.ll_state_match_shape _ _;
  let cont = from `SZ.size_lt` to in
  wc bout (fun bh ->
  with_local from (fun bfrom ->
  with_local true (fun b_no_interrupt ->
  with_local cont (fun bcont ->
    intro_impl_for_inv_aux_true cl inv from to f vbin.contents h bout from cont h;
    rewrite
      (impl_for_inv0 cl inv p from to f bin vbin bh h bfrom b_no_interrupt bcont cont)
      (impl_for_inv cl inv p from to f bin vbin bh h bfrom b_no_interrupt bcont cont);
    Steel.ST.Loops.while_loop
      (impl_for_inv cl inv p from to f bin vbin bh h bfrom b_no_interrupt bcont)
      (impl_for_test cl inv p from to f bin vbin bh h bfrom b_no_interrupt bcont)
      (impl_for_body cl inv p from to f bin vbin bh h bfrom b_no_interrupt bcont fi wl ws);
    impl_for_post cl inv p from to f bin vbin bh h bfrom b_no_interrupt bcont kpre kpost k_success k_failure prf wl
  ))))

[@@__reduce__]
let parse_nlist0
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_filter_kind parse_list_kind) (nlist n t))
= parse_list p `parse_filter` (fun l -> List.Tot.length l = n) `parse_synth` (fun x -> (x <: (nlist n t)))

let parse_nlist
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot (parser (parse_filter_kind parse_list_kind) (nlist n t))
= parse_nlist0 n p

let intro_nlist
  (#opened: _)
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#vb: v parse_list_kind (list t))
  (b: byte_array)
: STGhost (v (parse_filter_kind parse_list_kind) (nlist n t)) opened
    (aparse (parse_list p) b vb)
    (fun vb' -> aparse (parse_nlist n p) b vb')
    (List.Tot.length vb.contents == n)
    (fun vb' ->
      array_of' vb' == array_of' vb /\
      (vb'.contents <: list t) == vb.contents
    )
= let _ = intro_filter _ (fun l -> List.Tot.length l = n) b in
  let _ = intro_synth _ (fun (x: parse_filter_refine _) -> (x <: (nlist n t))) b () in
  rewrite_aparse b (parse_nlist n p)

let elim_nlist
  (#opened: _)
  (n: nat)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#vb: v (parse_filter_kind parse_list_kind) (nlist n t))
  (b: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_nlist n p) b vb)
    (fun vb' -> aparse (parse_list p) b vb')
    True
    (fun vb' ->
      array_of' vb' == array_of' vb /\
      (vb.contents <: list t) == vb'.contents
    )
= let _ = rewrite_aparse b (parse_nlist0 n p) in
  let _ = elim_synth _ _ b () in
  elim_filter _ _ b

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction
let impl_list_index
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (jp: jumper p)
  (n: SZ.size_t)
  (idx: (i: SZ.size_t { SZ.size_v i < SZ.size_v n }))
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (fi: fold_impl_t cl p f)
: Pure (fold_impl_t cl (parse_nlist (SZ.size_v n) p) (fold_list_index inv (SZ.size_v n) (SZ.size_v idx) f))
    (requires  k.parser_kind_subkind == Some ParserStrong)
    (ensures (fun _ -> True))
= fun kpre kpost #vbin bin bout h k_success k_failure ->
  let _ = elim_nlist _ _ bin in
  let b = list_nth jp bin idx in
  let _ = gen_elim () in
  let vbin_l = vpattern_replace (aparse (parse_list p) bin) in
  let vb = vpattern_replace (aparse p b) in
  let vbin_r = vpattern_replace (aparse (parse_list p) (list_nth_tail _ _ _ _)) in
  let bin_r = vpattern_replace_erased (fun bin_r -> aparse (parse_list p) bin_r vbin_r) in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse (parse_list p) bin vbin_l `star`
      aparse p b vb `star`
      aparse (parse_list p) bin_r vbin_r)
    (fun _ -> aparse (parse_nlist (SZ.size_v n) p) bin vbin)
  = let _ = intro_cons p b bin_r in
    let _ = list_append p bin b in
    let _ = intro_nlist (SZ.size_v n) p bin in
    rewrite
      (aparse (parse_nlist (SZ.size_v n) p) bin _)
      (aparse (parse_nlist (SZ.size_v n) p) bin vbin)
  in
  fi
    (kpre `star`
      aparse (parse_list p) bin vbin_l `star`
      aparse (parse_list p) bin_r vbin_r)
    kpost
    b bout h
    (fun out' h' v' ->
      restore ();
      k_success out' h' v'
    )
    (fun h' v' ->
      restore ();
      k_failure h' v'
    )

#pop-options

inline_for_extraction
let impl_list_index_of
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (jp: jumper p)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (fi: fold_impl_t cl p f) 
  (n: SZ.size_t)
  (idx: Ghost.erased ((i: nat { i < SZ.size_v n }) -> Tot (i: nat { i < SZ.size_v n })))
  (idx' : (i: SZ.size_t) -> Pure SZ.size_t (requires SZ.size_v i < SZ.size_v n) (ensures fun j -> SZ.size_v j == Ghost.reveal idx (SZ.size_v i)))
  (j: SZ.size_t {SZ.size_v j < SZ.size_v n})
: Pure (fold_impl_t cl (parse_nlist (SZ.size_v n) p) (fold_list_index_of inv f (SZ.size_v n) idx (SZ.size_v j)))
    (requires  k.parser_kind_subkind == Some ParserStrong)
    (ensures (fun _ -> True))
= impl_list_index cl inv jp n (idx' j) f fi

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
let impl_for_list
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (#k: parser_kind)
  (#p: parser k t)
  (j: jumper p)
  (fi: fold_impl_t cl p f)
  (prf: fold_state_inc cl f)
  (idx: array_index_fn)
  (wc: with_ll_state_ptr_t cl inv)
  (wl: load_ll_state_ptr_t cl inv)
  (ws: store_ll_state_ptr_t cl inv)
: Pure (fold_impl_t cl (parse_vldata 4 (parse_list p)) (fold_for_list inv f idx.array_index_f_nat))
    (requires  k.parser_kind_subkind == Some ParserStrong)
    (ensures (fun _ -> True))
= fun kpre kpost #vbin bin bout h k_success k_failure ->
  let bin_l = elim_vldata 4 (parse_list p) bin in
  let _ = gen_elim () in
  let vl_sz = vpattern_replace (aparse (parse_bounded_integer 4) bin) in
  let _ = vpattern_replace (aparse (parse_list p) bin_l) in
  let in_sz = read_bounded_integer 4 bin in
  let n = list_length j bin_l (SZ.mk_size_t in_sz) in
  let vl_l = intro_nlist (SZ.size_v n) _ bin_l in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse (parse_bounded_integer 4) bin vl_sz `star`
      aparse (parse_nlist (SZ.size_v n) p) bin_l vl_l)
    (fun _ -> aparse (parse_vldata 4 (parse_list p)) bin vbin)
  =
    let _ = elim_nlist _ _ bin_l in
    let _ = intro_vldata 4 (parse_list p) bin bin_l in
    let vbin' = rewrite_aparse bin (parse_vldata 4 (parse_list p)) in
    rewrite (aparse _ bin _) (aparse (parse_vldata 4 (parse_list p)) bin vbin)
  in
  impl_for
    cl inv
    (parse_nlist (SZ.size_v n) p)
    SZ.zero_size
    n
    (fold_list_index_of inv f (SZ.size_v n) (idx.array_index_f_nat (SZ.size_v n)))
    (fun x i s -> prf (List.Tot.index i (idx.array_index_f_nat (SZ.size_v n) x)) s)
    (impl_list_index_of cl inv j f fi n (idx.array_index_f_nat (SZ.size_v n)) (idx.array_index_f_sz n))
    wc wl ws
    (kpre `star` aparse (parse_bounded_integer 4) bin vl_sz)
    kpost
    bin_l bout h
    (fun out' h' v' ->
      restore ();
      k_success out' h' v'
    )
    (fun h' v' ->
      restore ();
      k_failure h' v'
    )

#pop-options

(* list fold *)

let impl_list_hole_inv_prop
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (h0: state_t inv)
  (l: list t)
  (h: state_t inv)
: Tot prop
=
  fold_list inv f l h0 == ((), h)

[@@__reduce__]
let impl_list_hole_inv_true
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (bh: ll_state_ptr)
  (h0: state_t inv)
  (l: list t)
: Tot vprop
= exists_ (fun (h: state_t inv) -> exists_ (fun out ->
    cl.ll_state_match h out `star`
    cl.ll_state_pts_to bh out `star`
    pure (
      impl_list_hole_inv_prop inv f h0 l h
    )
  ))

[@@__reduce__]
let impl_list_hole_inv_false
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (bh: ll_state_ptr)
  (h0: state_t inv)
  (l: list t)
: Tot vprop
= 
  exists_ (cl.ll_state_pts_to bh) `star`
  exists_ (fun h ->
    cl.ll_state_failure h `star`
    pure (impl_list_hole_inv_prop inv f h0 l h)
  )

let impl_list_hole_inv
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (bh: ll_state_ptr)
  (h0: state_t inv)
  (cont: bool)
  (l: list t)
: Tot vprop
= if cont
  then impl_list_hole_inv_true cl inv f bh h0 l
  else impl_list_hole_inv_false cl inv f bh h0 l

inline_for_extraction
let impl_list_post_true
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (#k: parser_kind)
  (p: parser k t)
  (w: load_ll_state_ptr_t cl inv)
  (#vbin: _)
  (bin: byte_array)
  (h: Ghost.erased (state_t inv))
  (kpre kpost: vprop)
  (k_success: (
    (out': ll_state) ->
    (h': Ghost.erased (state_t inv)) ->
    (v: unit) ->
    ST unit
      (kpre `star` aparse (parse_vldata 4 (parse_list p)) bin vbin `star`
        cl.ll_state_match h' out')
      (fun _ -> kpost)
      (
        fold_list inv f vbin.contents h == (v, Ghost.reveal h')
      )
      (fun _ -> True)
  ))
  (bh: ll_state_ptr)
  (cont: bool)
  (l: Ghost.erased (list t))
: ST unit
    (kpre `star` aparse (parse_vldata 4 (parse_list p)) bin vbin `star`
      impl_list_hole_inv cl inv f bh h cont l)
    (fun _ ->
      kpost `star`
      exists_ (cl.ll_state_pts_to bh)
    )
    (cont == true /\
      Ghost.reveal l == vbin.contents)
    (fun _ -> True)
=
  rewrite
    (impl_list_hole_inv cl inv f bh h cont l)
    (impl_list_hole_inv_true cl inv f bh h l);
  let _ = gen_elim () in
  cl.ll_state_match_shape _ _;
  w bh (fun out' ->
    vpattern_rewrite (cl.ll_state_match _) out';
    k_success _ _ ()
  )

inline_for_extraction
let impl_list_post_false
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (#k: parser_kind)
  (p: parser k t)
  (#vbin: _)
  (bin: byte_array)
  (h: Ghost.erased (state_t inv))
  (kpre kpost: vprop)
  (k_failure: (
    (h': Ghost.erased (state_t inv)) ->
    (v: Ghost.erased unit) ->
    ST unit
      (kpre `star` aparse (parse_vldata 4 (parse_list p)) bin vbin `star` cl.ll_state_failure h')
      (fun _ -> kpost)
      (
        fold_list inv f vbin.contents h == (Ghost.reveal v, Ghost.reveal h')
      )
      (fun _ -> True)
  ))
  (bh: ll_state_ptr)
  (cont: bool)
  (l: Ghost.erased (list t))
: ST unit
    (kpre `star` aparse (parse_vldata 4 (parse_list p)) bin vbin `star`
      impl_list_hole_inv cl inv f bh h cont l)
    (fun _ ->
      kpost `star`
      exists_ (cl.ll_state_pts_to bh)
    )
    (cont == false /\
      Ghost.reveal l == vbin.contents)
    (fun _ -> True)
=
  rewrite
    (impl_list_hole_inv cl inv f bh h cont l)
    (impl_list_hole_inv_false cl inv f bh h l);
  let _ = gen_elim () in
  k_failure _ ()

let rec fold_list_append
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv (inv))
  (state: state_t inv)
  (l1 l2: list t)
: Lemma
  (ensures (fold_list inv f (l1 `List.Tot.append` l2) state ==
    (let (_, state1) = fold_list inv f l1 state in
    fold_list inv f l2 state1)))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a :: q ->
    let (_, state0) = f a state in
    fold_list_append inv f state0 q l2

let fold_list_snoc
  #state_i #state_t
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv (inv))
  (state: state_t inv)
  (l: list t)
  (x: t)
: Lemma
  (ensures (fold_list inv f (List.Tot.snoc (l, x)) state ==
    (let (_, state1) = fold_list inv f l state in
    f x state1)))
= fold_list_append inv f state l [x]

inline_for_extraction
let impl_list_body_false
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (prf: fold_state_inc cl f)
  (#k: parser_kind)
  (p: parser k t)
  (bh: ll_state_ptr)
  (h0: Ghost.erased (state_t inv))
  (#opened: _)
  (va: v k t { AP.length (array_of' va) > 0 })
  (a: byte_array)
  (l: Ghost.erased (list t))
: STGhostT unit opened
    (aparse p a va `star` impl_list_hole_inv cl inv f bh h0 false l)
    (fun _ -> aparse p a va `star` impl_list_hole_inv cl inv f bh h0 false (List.Tot.snoc (Ghost.reveal l, va.contents)))
= rewrite
    (impl_list_hole_inv cl inv f bh h0 false l)
    (impl_list_hole_inv_false cl inv f bh h0 l);
  let _ = gen_elim () in
  fold_list_snoc inv f h0 l va.contents;
  prf va.contents (sndp (fold_list inv f l h0));
  cl.ll_state_failure_inc _ (sndp (fold_list inv f (List.Tot.snoc (Ghost.reveal l, va.contents)) h0));
  rewrite
    (impl_list_hole_inv_false cl inv f bh h0 (List.Tot.snoc (Ghost.reveal l, va.contents)))
    (impl_list_hole_inv cl inv f bh h0 false (List.Tot.snoc (Ghost.reveal l, va.contents)))

inline_for_extraction
let impl_list_body_true
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (#k: parser_kind)
  (p: parser k t)
  (impl_f: fold_impl_t cl p f)
  (wl: load_ll_state_ptr_t cl inv)
  (ws: store_ll_state_ptr_t cl inv)
  (bh: ll_state_ptr)
  (h0: Ghost.erased (state_t inv))
  (va: v k t { AP.length (array_of' va) > 0 })
  (a: byte_array)
  (l: Ghost.erased (list t))
: STT bool
    (aparse p a va `star` impl_list_hole_inv cl inv f bh h0 true l)
    (fun res -> aparse p a va `star` impl_list_hole_inv cl inv f bh h0 res (List.Tot.snoc (Ghost.reveal l, va.contents)))
= with_local true (fun bres ->
    rewrite
      (impl_list_hole_inv cl inv f bh h0 true l)
      (impl_list_hole_inv_true cl inv f bh h0 l);
    let _ = gen_elim () in
    cl.ll_state_match_shape _ _;
    wl bh (fun out ->
      fold_list_snoc inv f h0 l va.contents;
      vpattern_rewrite (cl.ll_state_match _) out;
      impl_f
        (cl.ll_state_pts_to bh out `star` R.pts_to bres full_perm true)
        (aparse p a va `star` exists_ (fun res -> R.pts_to bres full_perm res `star` impl_list_hole_inv cl inv f bh h0 res (List.Tot.snoc (Ghost.reveal l, va.contents))))
        a
        out
        _
        (fun out' h' _ ->
          cl.ll_state_match_shape _ _;
          ws bh out' ;
          rewrite
            (impl_list_hole_inv_true cl inv f bh h0 (List.Tot.snoc (Ghost.reveal l, va.contents)))
            (impl_list_hole_inv cl inv f bh h0 true (List.Tot.snoc (Ghost.reveal l, va.contents)));
          noop ()
        )
        (fun h' _ ->
          R.write bres false;
          rewrite
            (impl_list_hole_inv_false cl inv f bh h0 (List.Tot.snoc (Ghost.reveal l, va.contents)))
            (impl_list_hole_inv cl inv f bh h0 false (List.Tot.snoc (Ghost.reveal l, va.contents)));
          noop ()
        )
      ;
      let _ = gen_elim () in
      let res = R.read bres in
      rewrite
        (impl_list_hole_inv cl inv f bh h0 _ _)
        (impl_list_hole_inv cl inv f bh h0 res (List.Tot.snoc (Ghost.reveal l, va.contents)));
      return res
  ))

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction
let impl_list
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: Ghost.erased (fold_t state_t t unit inv inv))
  (prf: fold_state_inc cl f)
  (#k: parser_kind)
  (p: parser k t)
  (impl_f: fold_impl_t cl p f)
  (j: jumper p) // MUST be computed OUTSIDE of impl_list
  (wc: with_ll_state_ptr_t cl inv) // same
  (wl: load_ll_state_ptr_t cl inv)
  (ws: store_ll_state_ptr_t cl inv)
: Pure (fold_impl_t cl (parse_vldata 4 (parse_list p)) (fold_list inv f))
    (requires (k.parser_kind_subkind == Some ParserStrong))
    (ensures (fun _ -> True))
= fun kpre kpost #vbin bin bout h k_success k_failure ->
  let _ = rewrite_aparse bin (parse_vldata 4 (parse_list p)) in
  let bin_l = elim_vldata 4 (parse_list p) bin in
  let _ = gen_elim () in
  let vl_sz = vpattern_replace (aparse (parse_bounded_integer 4) bin) in
  let vl_l = vpattern_replace (aparse (parse_list p) bin_l) in
  let restore (#opened: _) () : STGhostT unit opened
    (aparse (parse_bounded_integer 4) bin vl_sz `star`
      aparse (parse_list p) bin_l vl_l)
    (fun _ -> aparse (parse_vldata 4 (parse_list p)) bin vbin)
  =
    let _ = intro_vldata 4 (parse_list p) bin bin_l in
    vpattern_rewrite (aparse _ bin) vbin
  in
  let in_sz = read_bounded_integer 4 bin in
  cl.ll_state_match_shape _ _;
  wc bout (fun bh ->
    noop ();
    rewrite
      (impl_list_hole_inv_true cl inv f bh h [])
      (impl_list_hole_inv cl inv f bh h true []);
    let cont = list_iter_with_interrupt
      j
      (impl_list_hole_inv cl inv f bh h)
      (impl_list_body_true cl inv f p impl_f wl ws bh h)
      (impl_list_body_false cl inv f prf p bh h)
      bin_l
      (SZ.mk_size_t in_sz)
    in
    restore ();
    if cont
    then impl_list_post_true cl inv f p wl bin h kpre kpost k_success bh cont _
    else impl_list_post_false cl inv f p bin h kpre kpost k_failure bh cont _
  )

#pop-options

(* Implementing programs *)

[@@specialize]
noeq
type action_impl
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (action_t: (t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
  (action_sem: ((#t: Type) -> (#pre: _) -> (#post: _) -> action_t t pre post -> stt state_t t pre post))
= {
    a_inc: (
      (#t: Type) ->
      (#pre: state_i) ->
      (#post: state_i) ->
      (a: action_t t pre post) ->
      stt_state_inc cl (action_sem a)
    );
    a_impl: (
      (#t: Type) ->
      (#pre: state_i) ->
      (#post: state_i) ->
      (a: action_t t pre post) ->
      stt_impl_t cl (action_sem a)
    );
  }

[@@specialize]
noeq
type ll_state_ptr_ops
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
= {
    with_ll_state_ptr: (
      (inv: state_i) ->
      with_ll_state_ptr_t cl inv
    );
    load_ll_state_ptr: (
      (inv: state_i) ->
      load_ll_state_ptr_t cl inv
    );
    store_ll_state_ptr: (
      (inv: state_i) ->
      store_ll_state_ptr_t cl inv
    );
  }

let rec fold_list_inc'
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (prf: fold_state_inc cl f)
  (input: list t)
  (s: state_t inv)
: Lemma
  (ensures (
    let (v, s') = fold_list inv f input s in
    s' `cl.state_ge` s
  ))
  (decreases input)
= match input with
  | [] -> cl.state_ge_refl s
  | hd :: tl ->
    prf hd s;
    let (_, s1) = f hd s in
    fold_list_inc' cl inv f prf tl s1;
    let (_, s2) = fold_list inv f tl s1 in
    cl.state_ge_trans s2 s1 s

let fold_list_inc
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (prf: fold_state_inc cl f)
: Tot (fold_state_inc cl (fold_list inv f))
= fold_list_inc' cl inv f prf

let fold_for_list_inc
  #state_i #state_t #ll_state #ll_state_ptr
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (inv: state_i)
  (#t: Type)
  (f: fold_t state_t t unit inv inv)
  (prf: fold_state_inc cl f)
  (idx: ((n: nat) -> (x: nat {x < n}) -> (y: nat {y < n})))
: Tot (fold_state_inc cl (fold_for_list inv f idx))
= fun l s ->
  let n = List.Tot.length l in
  fold_for_inc cl inv 0 n (fold_list_index_of inv f n (idx n))
    (fun i l s -> prf (List.Tot.index l (idx n i)) s)
    l s

let rec prog_inc
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#action_t: (t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
  (#action_sem: ((#t: Type) -> (#pre: _) -> (#post: _) -> action_t t pre post -> stt state_t t pre post))
  (a_cl: action_impl cl action_t action_sem)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ty: typ)
  (p: prog state_t action_t ty ret_t pre post)
: Tot (fold_state_inc cl (sem action_sem p))
  (decreases p)
= fun input s ->
  match p with
  | PRet _ -> cl.state_ge_refl s
  | PAction a ->
    a_cl.a_inc a s
  | PBind f g ->
    prog_inc a_cl f input s;
    let (v1, s1) = sem action_sem f input s in
    prog_inc a_cl (g v1) input s1;
    let (_, s2) = sem action_sem (g v1) input s1 in
    cl.state_ge_trans s2 s1 s
  | PU8 _ -> cl.state_ge_refl s
  | PIf x ptrue pfalse ->
    if x
    then prog_inc a_cl (ptrue ()) input s
    else prog_inc a_cl (pfalse ()) input s
  | PPair #_ #_ #_ #t1 #t2 f1 f2 ->
    let (input1, input2) = (input <: type_of_typ (TPair t1 t2)) in
    prog_inc a_cl f1 input1 s;
    let (v1, s1) = sem action_sem f1 input1 s in
    prog_inc a_cl (f2 v1) input2 s1;
    let (_, s2) = sem action_sem (f2 v1) input2 s1 in
    cl.state_ge_trans s2 s1 s
  | PList i f ->
    fold_list_inc
      cl
      (sem action_sem f)
      (fun i s -> prog_inc a_cl f i s)
      input
      s
  | PListFor i idx f ->
    fold_for_list_inc
      cl
      _
      (sem action_sem f)
      (prog_inc a_cl f)
      idx.array_index_f_nat
      input
      s
  | PChoice #_ #_ #_ #t f ->
    let (| tag, payload |) = (input <: type_of_typ (TChoice t)) in
    prog_inc a_cl (f tag) payload s

let rec parser_of_typ (t: typ) : Tot (parser pkind (type_of_typ t)) =
  match t returns parser pkind (type_of_typ t) with
  | TU8 -> weaken _ parse_u8
  | TPair t1 t2 -> weaken _ (nondep_then (parser_of_typ t1) (parser_of_typ t2))
  | TList t' ->
    weaken _ (parse_vldata 4 (parse_list (parser_of_typ t')))
  | TChoice f -> weaken _ (parse_dtuple2 parse_bool #_ #(type_of_payload' f) (fun x -> parser_of_typ (f x)))

inline_for_extraction
let jump_ifthenelse
  (#k: parser_kind)
  (#t: bool -> Type)
  (p: (x: bool) -> parser k (t x))
  (jtrue: jumper (p true))
  (jfalse: jumper (p false))
  (x: bool)
: Tot (jumper (p x))
= fun a ->
  if x
  then jtrue a
  else jfalse a

[@@specialize]
let rec jumper_of_typ (t: typ) : Tot (jumper (parser_of_typ t)) =
  match t returns jumper (parser_of_typ t) with
  | TU8 -> jump_weaken _ (jump_constant_size parse_u8 SZ.one_size) ()
  | TPair t1 t2 -> jump_weaken _ (jump_pair (jumper_of_typ t1) (jumper_of_typ t2)) ()
  | TList t' ->
    jump_weaken _
      (jump_vldata_gen 4 (unconstrained_bounded_integer 4) (parse_list (parser_of_typ t')))
      ()
  | TChoice f ->
    jump_weaken _
      (jump_dtuple2
        (jump_constant_size parse_bool SZ.one_size)
        read_bool
        _
        (jump_ifthenelse (fun x -> parser_of_typ (f x)) (jumper_of_typ (f true)) (jumper_of_typ (f false))))
      ()

[@@specialize]
let rec impl
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#action_t: (t: Type) -> (pre: state_i) -> (post: state_i) -> Type)
  (#action_sem: ((#t: Type) -> (#pre: _) -> (#post: _) -> action_t t pre post -> stt state_t t pre post))
  (a_cl: action_impl cl action_t action_sem)
  (ptr_cl: ll_state_ptr_ops cl)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ty: typ)
  (p: prog state_t action_t ty ret_t pre post)
: Tot (fold_impl_t cl #ret_t #pre #post #(type_of_typ ty) #pkind (parser_of_typ ty) (sem action_sem p))
  (decreases p)
= match p with
  | PRet #_ #_ #_ #_ #i v ->
      coerce _ (impl_action cl (ret v) (impl_ret cl i v) (parser_of_typ ty))
  | PAction a ->
      coerce _ (impl_action cl _ (a_cl.a_impl a) (parser_of_typ ty))
  | PBind f g ->
      coerce _ (impl_bind cl (parser_of_typ ty) (sem action_sem f) (coerce _ (impl a_cl ptr_cl f)) (fun x -> sem action_sem (g x)) (fun x -> coerce _ (impl a_cl ptr_cl (g x))) (fun x -> prog_inc a_cl (g x)) <: fold_impl_t cl (parser_of_typ ty) (sem action_sem (PBind f g)))
  | PIf x ptrue pfalse ->
      coerce _ (impl_if cl x (fun _ -> sem action_sem (ptrue ())) (parser_of_typ ty) (fun _ -> coerce _ (impl a_cl ptr_cl (ptrue ()))) (fun _ -> sem action_sem (pfalse ())) (fun _ -> coerce _ (impl a_cl ptr_cl (pfalse ()))))
  | PU8 i ->
      coerce _ (impl_rewrite_parser cl (fold_read ()) (impl_read cl i read_u8) (parser_of_typ ty))
  | PPair #_ #_ #_ #t1 #t2 f1 f2 ->
      assert_norm (sem action_sem (PPair f1 f2) == fold_pair (sem action_sem f1) (fun x -> sem action_sem (f2 x)));
      coerce _
        (impl_rewrite_parser
          cl
          (fold_pair (sem action_sem f1) (fun x -> sem action_sem (f2 x)))
          (impl_pair cl
            (sem action_sem f1)
            (impl a_cl ptr_cl f1)
            (jumper_of_typ t1)
            (fun x -> sem action_sem (f2 x))
            (fun x -> impl a_cl ptr_cl (f2 x))
            (fun x -> prog_inc a_cl (f2 x))
          )
          (parser_of_typ (TPair t1 t2))
        )
  | PList #_ #_ #_ #ty inv f ->
      coerce _
        (impl_rewrite_parser
          cl
          (fold_list inv (sem action_sem f))
          (impl_list
            cl
            inv
            (sem action_sem f)
            (prog_inc a_cl f)
            (parser_of_typ ty)
            (impl a_cl ptr_cl f)
            (jumper_of_typ ty)
            (ptr_cl.with_ll_state_ptr inv)
            (ptr_cl.load_ll_state_ptr inv)
            (ptr_cl.store_ll_state_ptr inv)
          )
          (parser_of_typ (TList ty))
        )
  | PListFor #_ #_ #_ #ty inv idx f ->
      coerce _
        (impl_rewrite_parser
          cl
          (fold_for_list inv (sem action_sem f) idx.array_index_f_nat)
          (impl_for_list
            cl
            inv
            (sem action_sem f)
            (jumper_of_typ ty)
            (impl a_cl ptr_cl f)
            (prog_inc a_cl f)
            idx
            (ptr_cl.with_ll_state_ptr inv)
            (ptr_cl.load_ll_state_ptr inv)
            (ptr_cl.store_ll_state_ptr inv)
          )
          (parser_of_typ (TList ty))
        )
  | PChoice #_ #_ #_ #t f ->
      assert_norm (sem action_sem (PChoice f) == fold_choice #_ #_ #_ #(type_of_payload' t) (fun x -> sem action_sem (f x)));
      assert_norm (parser_of_typ (TChoice t) == weaken pkind (parse_dtuple2 parse_bool #_ #(type_of_payload' t) (fun x -> parser_of_typ (t x))));
      coerce _
        (impl_rewrite_parser
          cl
          (fold_choice #_ #_ #_ #(type_of_payload' t) (fun x -> sem action_sem (f x)))
          #_
          #(parse_dtuple2 parse_bool #_ #(type_of_payload' t) (fun x -> parser_of_typ (t x)))
          (impl_choice
            cl
            #(type_of_payload' t)
            (fun x -> sem action_sem (f x))
            (fun x -> parser_of_typ (t x))
            (fun x -> impl a_cl ptr_cl (f x))
          )
          (parser_of_typ (TChoice t))
        )

inline_for_extraction
let mk_ll_state_t
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (vpre: vprop)
  (#pre: state_i)
  (h: state_t pre)
: Tot Type
= (#kpre: vprop) ->
  (#tret: Type) ->
  (#kpost: (tret -> vprop)) ->
  (k: (
    (out: ll_state) ->
    STT tret
      (kpre `star` cl.ll_state_match h out)
      kpost
  )) ->
  STF tret (kpre `star` vpre) kpost True (fun _ -> True)

let extract_impl_unit_post
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (pre post: state_i)
  (f: stt state_t unit pre post)
  (h: state_t pre)
  (b: bool)
: Tot vprop
= let h' = get_return_state f h in
  if b
  then exists_ (cl.ll_state_match h')
  else cl.ll_state_failure h'

inline_for_extraction
let extract_impl_stt'_unit
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (f: Ghost.erased (stt state_t unit pre post))
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t cl vpre h)
  (kpre0: vprop)
  (fi: (kpre: vprop) -> (kpost: vprop) -> stt_impl_t' cl f (kpre0 `star` kpre) kpost)
: STT bool
    (vpre `star` kpre0)
    (fun res -> extract_impl_unit_post cl pre post f h res `star` kpre0)
= mk (fun out ->
    with_local true (fun bres ->
      fi
        (R.pts_to bres full_perm true)
        (kpre0 `star` exists_ (fun res ->
          R.pts_to bres full_perm res `star`
          extract_impl_unit_post cl pre post f h res
        ))
        out
        h
        (fun out' h' _ ->
          rewrite
            (exists_ (cl.ll_state_match h'))
            (extract_impl_unit_post cl pre post f h true);
          noop ()
        )
        (fun h' _ ->
          R.write bres false;
          rewrite
            (cl.ll_state_failure h')
            (extract_impl_unit_post cl pre post f h false);
          noop ()
        );
      let _ = gen_elim () in
      let res = R.read bres in
      vpattern_rewrite (extract_impl_unit_post cl pre post f h) res;
      return res
    )
  )

inline_for_extraction
let extract_impl_stt_unit
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#f: Ghost.erased (stt state_t unit pre post))
  (fi: stt_impl_t cl f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t cl vpre h)
: STT bool
    (vpre)
    (fun res -> extract_impl_unit_post cl pre post f h res)
= extract_impl_stt'_unit
    f mk emp fi

inline_for_extraction
let extract_impl_fold_unit
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#t: Type)
  (#f: Ghost.erased (fold_t state_t t unit pre post))
  (#k: parser_kind)
  (#p: parser k t)
  (fi: fold_impl_t cl p f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t cl vpre h)
  (#vbin: v k t)
  (bin: byte_array)
: STT bool
    (vpre `star` aparse p bin vbin)
    (fun res -> extract_impl_unit_post cl pre post (Ghost.reveal f vbin.contents) h res `star` aparse p bin vbin)
= extract_impl_stt'_unit
    (Ghost.reveal f vbin.contents)
    mk
    (aparse p bin vbin)
    (fun kpre kpost -> fi kpre kpost #vbin bin)

let extract_impl_post
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (pre post: state_i)
  (#ret_t: Type)
  (r: R.ref ret_t)
  (f: stt state_t ret_t pre post)
  (h: state_t pre)
  (b: bool)
: Tot vprop
= let h' = get_return_state f h in
  let v = get_return_value f h in
  if b
  then exists_ (cl.ll_state_match h') `star` R.pts_to r full_perm v
  else cl.ll_state_failure h' `star` exists_ (R.pts_to r full_perm)

inline_for_extraction
let extract_impl_stt'
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#rett: Type)
  (f: Ghost.erased (stt state_t rett pre post))
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t cl vpre h)
  (kpre0: vprop)
  (fi: (kpre: vprop) -> (kpost: vprop) -> stt_impl_t' cl f (kpre0 `star` kpre) kpost)
  (r: R.ref rett)
: STT bool
    (vpre `star` kpre0 `star` exists_ (R.pts_to r full_perm))
    (fun res -> extract_impl_post cl pre post r f h res `star` kpre0)
= mk (fun out ->
    with_local true (fun bres ->
      fi
        (R.pts_to bres full_perm true `star`
          exists_ (R.pts_to r full_perm))
        (kpre0 `star` exists_ (fun res ->
          R.pts_to bres full_perm res `star`
          extract_impl_post cl pre post r f h res
        ))
        out
        h
        (fun out' h' v ->
          let _ = gen_elim () in
          R.write r v;
          rewrite
            (exists_ (cl.ll_state_match h') `star` R.pts_to r full_perm v)
            (extract_impl_post cl pre post r f h true);
          noop ()
        )
        (fun h' _ ->
          R.write bres false;
          rewrite
            (cl.ll_state_failure h' `star` exists_ (R.pts_to r full_perm))
            (extract_impl_post cl pre post r f h false);
          noop ()
        );
      let _ = gen_elim () in
      let res = R.read bres in
      vpattern_rewrite (extract_impl_post cl pre post r f h) res;
      return res
    )
  )

inline_for_extraction
let extract_impl_stt
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#t: Type)
  (#f: Ghost.erased (stt state_t t pre post))
  (fi: stt_impl_t cl f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t cl vpre h)
  (r: R.ref t)
: STT bool
    (vpre `star` exists_ (R.pts_to r full_perm))
    (fun res -> extract_impl_post cl pre post r f h res)
= extract_impl_stt'
    f mk emp fi r

inline_for_extraction
let extract_impl_fold
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type)
  (#cl: low_level_state state_i state_t ll_state ll_state_ptr)
  (#pre #post: state_i)
  (#t: Type)
  (#rett: Type)
  (#f: Ghost.erased (fold_t state_t t rett pre post))
  (#k: parser_kind)
  (#p: parser k t)
  (fi: fold_impl_t cl p f)
  (#vpre: vprop)
  (#h: Ghost.erased (state_t pre))
  (mk: mk_ll_state_t cl vpre h)
  (vbin: v k t)
  (bin: byte_array)
  (r: R.ref rett)
: STT bool
    (vpre `star` aparse p bin vbin `star` exists_ (R.pts_to r full_perm))
    (fun res -> extract_impl_post cl pre post r (Ghost.reveal f vbin.contents) h res `star` aparse p bin vbin)
= extract_impl_stt'
    (Ghost.reveal f vbin.contents)
    mk
    (aparse p bin vbin)
    (fun kpre kpost -> fi kpre kpost #vbin bin)
    r
