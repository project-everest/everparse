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
  (#gl: ll_state) ->
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
let store_ll_state_ptr
  (#state_i: Type) (#state_t: state_i -> Type) (#ll_state: Type) (#ll_state_ptr: Type) (#ll_fstate: Type)
  (cl: low_level_state state_i state_t ll_state ll_state_ptr ll_fstate)
  (i: state_i)
: Tot Type
= (i: state_i) ->
  (#gl: ll_state) ->
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

let fold_choice'
  #state_i #state_t
  (#ret_t: Type)
  (#t: bool -> Type)
  (#pre: state_i)
  (#post: _)
  (f: (x: bool) -> fold_t state_t (t x) ret_t pre post)
: Tot (fold_t state_t (dtuple2 bool t) ret_t pre post)
= fun w -> if (dfst w) then f true (dsnd w) else f false (dsnd w)

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
: Tot (fold_impl_t cl (parse_dtuple2 parse_bool p) (fold_choice' f))
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
