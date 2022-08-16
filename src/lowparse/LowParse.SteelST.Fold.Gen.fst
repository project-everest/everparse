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
  (state_i: Type) (state_t: state_i -> Type) (ll_state: Type) (ll_state_ptr: Type) (ll_fstate: Type)
= {
    ll_state_match: ((#i: state_i) -> (h: state_t i) -> ll_state -> vprop);
    ll_state_failure: ((#i: state_i) -> (h: state_t i) -> ll_fstate -> vprop);
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
      (#i1: state_i) -> (s1: state_t i1) -> (s: ll_fstate) ->
      (#i2: state_i) -> (s2: state_t i2) ->
      STGhost unit opened
        (ll_state_failure s1 s)
        (fun _ -> ll_state_failure s2 s)
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
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type) (#ll_fstate: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type) (#ll_fstate: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type) (#ll_fstate: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
    (bout': Ghost.erased ll_fstate) ->
    (h': Ghost.erased (state_t post)) ->
    (v: Ghost.erased ret_t) ->
    ST unit
      (kpre `star` cl.ll_state_failure h' bout')
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (#ret_t: Type)
  (i: state_i)
  (v: ret_t)
: Tot (stt_impl_t cl (ret #state_i #state_t #i v))
= fun kpre kpost bout h k_success k_failure ->
    k_success bout h v

inline_for_extraction
let impl_rewrite_parser
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (#ty: Type)
  (p: fold_t state_t ty ret_t pre post)
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
      (fun vb' h1 v1 ->
        restore ();
        k_failure vb' h1 v1)

inline_for_extraction
[@@noextract_to "krml"]
let impl_read
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (#ret_t: Type)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (#ret_t: Type)
  (#pre: state_i)
  (#post: state_i)
  (p: stt state_t ret_t pre post)
: Tot Type
= (s: state_t pre) ->
  Lemma
  (snd (p s) `cl.state_ge` s)

let fold_state_inc
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
let impl_bind
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (#ty: Type)
  (#kty: parser_kind)
  (pty: parser kty ty)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (#ret2: _)
  (#post2: _)
  (f: fold_t state_t ty ret1 pre1 post1)
  (impl_f: fold_impl_t cl pty f)
  (g: ((x: ret1) -> fold_t state_t ty ret2 post1 post2))
  (impl_g: ((x: ret1) -> fold_impl_t cl pty (g x)))
  (g_prf: ((x: ret1) -> fold_state_inc cl (g x)))
: Tot (fold_impl_t cl pty (bind_fold f g))
= fun kpre kpost (#vbin: v kty ty) (bin: byte_array) bout h k_success k_failure ->
    impl_f
      kpre kpost bin bout h
      (fun bout1 h1 v1 ->
        impl_g v1
          kpre kpost bin bout1 h1 k_success k_failure
      )
      (fun vb' h1 v1 ->
        let h2 = get_return_state (g v1 vbin.contents) h1 in
        let v2 = get_return_value (g v1 vbin.contents) h1 in
        g_prf v1 vbin.contents h1;
        cl.ll_state_failure_inc h1 vb' h2;
        k_failure vb' h2 v2
      )

inline_for_extraction
[@@noextract_to "krml"]
let impl_pair
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (#t1: Type)
  (#t2: Type)
  (#ret1: Type)
  (#pre1: _)
  (#post1: _)
  (f1: fold_t state_t t1 ret1 pre1 post1)
  (#k1: parser_kind)
  (#p1: parser k1 t1)
  (impl_f1: fold_impl_t cl p1 f1)
  (j1: jumper p1) // MUST be computed OUTSIDE of impl_pair
  (#ret2: _)
  (#post2: _)
  (f2: ((x: ret1) -> fold_t state_t t2 ret2 post1 post2))
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (impl_f2: ((x: ret1) -> fold_impl_t cl p2 (f2 x)))
  (f2_prf: ((x: ret1) -> fold_state_inc cl (f2 x))) 
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
        (fun vb' h2 v2 ->
          restore ();
          k_failure vb' h2 v2
        )
    )
    (fun vb' h1 v1 ->
      let h2 = get_return_state (f2 v1 vbin2.contents) h1 in
      let v2 = get_return_value (f2 v1 vbin2.contents) h1 in
      f2_prf v1 vbin2.contents h1;
      cl.ll_state_failure_inc h1 vb' h2;
      restore ();
      k_failure vb' h2 v2
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (#t: (bool -> Type))
  (#ret_t: Type)
  (#pre: _)
  (#post: _)
  (f: (x: bool) -> fold_t state_t (t x) ret_t pre post)
  (#k: parser_kind)
  (p: (x: bool) -> parser k (t x))
  (impl_f: (x: bool) -> fold_impl_t cl (p x) (f x))
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
    (fun vb' h' v' ->
      restore ();
      k_failure vb' h' v'
    )

module R = Steel.ST.Reference
module GR = Steel.ST.GhostReference

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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
    exists_ (cl.ll_state_failure h) `star`
    pure (impl_for_inv_aux_false_prop inv from0 to f l h0 h cont from)
  )

let impl_for_inv_aux_false
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (inv: state_i)
  (#t: Type)
  (from0: SZ.size_t) (to: SZ.size_t)
  (f: Ghost.erased ((x: nat { SZ.size_v from0 <= x /\ x < SZ.size_v to }) -> fold_t state_t t unit inv inv))
  (l: t)
  (h0: state_t inv)
  (cont: bool)
  (from: SZ.size_t)
  (h: state_t inv)
  (out: ll_fstate)
: STGhost unit opened
    (cl.ll_state_failure h out)
    (fun _ -> impl_for_inv_aux_false cl inv from0 to f l h0 cont from)
    (impl_for_inv_aux_false_prop inv from0 to f l h0 h cont from)
    (fun _ -> True)
= noop ();
  rewrite
    (impl_for_inv_aux_false0 cl inv from0 to f l h0 cont from)
    (impl_for_inv_aux_false cl inv from0 to f l h0 cont from)

let impl_for_inv_aux
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (#opened: _)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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

[@@erasable]
noeq
type impl_for_inv_aux_false_t
  (#state_i: _) (state_t: _)
  (ll_fstate: Type)
  (inv: state_i)
= {
    iff_from: SZ.size_t;
    iff_h: state_t inv;
    iff_out: ll_fstate;
  }

let elim_impl_for_inv_aux_false
  #opened
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
: STGhost (impl_for_inv_aux_false_t state_t ll_fstate inv) opened
    (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (fun r -> cl.ll_state_failure r.iff_h r.iff_out)
    (no_interrupt == false)
    (fun r ->
      impl_for_inv_aux_false_prop inv from0 to f l h0 r.iff_h cont r.iff_from
    )
=
  rewrite
    (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (exists_ (impl_for_inv_aux_false0 cl inv from0 to f l h0 cont));
  let from' = elim_exists () in
  let _ = gen_elim () in
  let h = vpattern (fun h -> cl.ll_state_failure h _) in
  let out' = vpattern (fun out' -> cl.ll_state_failure _ out') in
  let r = {
    iff_from = from';
    iff_h = h;
    iff_out = out';
  }
  in
  rewrite (cl.ll_state_failure _ _) (cl.ll_state_failure r.iff_h r.iff_out);
  r

let impl_for_inv_aux_cont_true
  (#opened: _)
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
      (cl.ll_state_failure _ _)
      (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
  end

[@@__reduce__]
let impl_for_inv0
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
      (fun vb' h2 _ ->
        R.write b_no_interrupt false;
        R.write bcont false;
        intro_impl_for_inv_aux_false cl inv from0 to f vl.contents h0 false from2 h2 vb';
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
  #opened
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
: STGhost (Ghost.erased (state_t inv & ll_fstate)) opened
    (impl_for_inv_aux cl inv from0 to f l h0 out from no_interrupt cont)
    (fun r -> cl.ll_state_failure (fstp r) (sndp r))
    (no_interrupt == false)
    (fun r ->
      fstp r == sndp (fold_for inv (SZ.size_v from0) (SZ.size_v to) f l h0)
    )
= let r0 = elim_impl_for_inv_aux_false _ _ _ _ _ _ _ _ _ _ _ in
  fold_for_inc_aux cl inv (SZ.size_v from0) (SZ.size_v to) f l h0 (SZ.size_v r0.iff_from) prf;
  let h = get_return_state (fold_for inv (SZ.size_v from0) (SZ.size_v to) f l) h0 in
  let res = Ghost.hide (Ghost.reveal h, r0.iff_out) in
  cl.ll_state_failure_inc r0.iff_h r0.iff_out h;
  rewrite (cl.ll_state_failure _ _) (cl.ll_state_failure (fstp res) (sndp res));
  res

inline_for_extraction
let impl_for_post
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
    (bout': Ghost.erased ll_fstate) ->
    (h': Ghost.erased (state_t inv)) ->
    (v: Ghost.erased unit) ->
    ST unit
      (kpre `star`
        aparse p bin vl `star`
        cl.ll_state_failure h' bout')
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
      k_failure (sndp r) (fstp r) ()
    end

inline_for_extraction
let impl_for
  #state_i #state_t #ll_state #ll_state_ptr #ll_fstate
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
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
