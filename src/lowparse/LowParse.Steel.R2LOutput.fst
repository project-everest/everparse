module LowParse.Steel.R2LOutput

module R = Steel.C.Reference

let t #base ap = R.ptr base SZ.size_t (Steel.C.Opt.opt_pcm #SZ.size_t)

let null _ = R.null _ _ _

let g_is_null x = Steel.C.Ref.ptr_is_null x

let vp_refine1
  (#base: Type)
  (#ap: AP.t base byte)
  (x: t ap)
  (_: SE.t_of SE.emp)
: Tot prop
= Steel.C.Ref.ptr_is_null x == false

let vp_refine2
  (#base: Type)
  (#ap: AP.t base byte)
  (x: t ap)
  (_: SE.t_of (SE.emp `SE.vrefine` vp_refine1 x))
  (xv: SE.normal (SE.t_of (R.pts_to_view x (Steel.C.Opt.opt_view SZ.size_t) `SE.star` AP.varrayptr ap)))
: Tot prop
= let (sz, v) = xv in AP.len v.AP.array == sz

[@@SE.__steel_reduce__; SE.__reduce__]
let vp_dep
  (#base: Type)
  (#ap: AP.t base byte)
  (x: t ap)
  (sq: SE.t_of (SE.emp `SE.vrefine` vp_refine1 x))
: Tot SE.vprop
=
  (R.pts_to_view x (Steel.C.Opt.opt_view SZ.size_t) `SE.star` AP.varrayptr ap)
    `SE.vrefine`
    vp_refine2 x sq
 
let vp_rewrite
  (#base: Type)
  (#ap: AP.t base byte)
  (x: t ap)
  (xv: SE.normal (SE.t_of (SE.emp `SE.vrefine` vp_refine1 x `SE.vdep` vp_dep x)))
: Tot (AP.array base byte)
= let (| _, (_, v) |) = xv in v.AP.array

[@@SE.__steel_reduce__; SE.__reduce__]
let vp0
  (#base: Type)
  (#ap: AP.t base byte)
  (x: t ap)
: Tot SE.vprop
= SE.emp `SE.vrefine` vp_refine1 x `SE.vdep` vp_dep x `SE.vrewrite` vp_rewrite x

let vp_hp x = SE.hp_of (vp0 x)
let vp_sel x = SE.sel_of (vp0 x)

let intro_vdep2
  (#opened: _)
  (v: SE.vprop)
  (g: SE.t_of v)
  (q: SE.vprop)
  (p: (SE.t_of v -> Tot SE.vprop))
: SEA.SteelGhost unit opened
    (v `SE.star` q)
    (fun _ -> SE.vdep v p)
    (requires (fun h ->
      g == h v /\
      q == p g
    ))
    (ensures (fun h _ h' ->
      let x2 = h' (SE.vdep v p) in
      g == h v /\
      q == p g /\
      dfst x2 == (h v) /\
      dsnd x2 == (h q)
    ))
= SEA.intro_vdep v q p

val intro_vp
  (#opened: _)
  (#base: Type)
  (#ap: AP.t base byte)
  (x: t ap)
  (sq: squash (Steel.C.Ref.ptr_is_null x == false))
: SEA.SteelGhost unit opened
    (AP.varrayptr ap `SE.star` R.pts_to_view x (Steel.C.Opt.opt_view SZ.size_t))
    (fun _ -> vp x)
    (requires (fun h ->
      AP.len (h (AP.varrayptr ap)).AP.array == h (R.pts_to_view x (Steel.C.Opt.opt_view SZ.size_t))
    ))
    (ensures (fun h _ h' ->
      h' (vp x) == (h (AP.varrayptr ap)).AP.array
    ))

let intro_vp #_ #_ #ap x sq =
  SEA.intro_vrefine SE.emp (vp_refine1 x);
  let g = SEA.gget (SE.emp `SE.vrefine` vp_refine1 x) in
  SEA.intro_vrefine (R.pts_to_view x (Steel.C.Opt.opt_view SZ.size_t) `SE.star` AP.varrayptr ap) (vp_refine2 x g);
  intro_vdep2
    (SE.emp `SE.vrefine` vp_refine1 x)
    g
    ((R.pts_to_view x (Steel.C.Opt.opt_view SZ.size_t) `SE.star` AP.varrayptr ap) `SE.vrefine` vp_refine2 x g)
    (vp_dep x);
  SEA.intro_vrewrite
    (SE.emp `SE.vrefine` vp_refine1 x `SE.vdep` vp_dep x)
    (vp_rewrite x);
  SEA.change_slprop_rel
    (vp0 x)
    (vp x)
    (fun u v -> u == v)
    (fun m -> 
      assert_norm (SE.hp_of (vp0 x) == SE.hp_of (vp x));
      assert_norm (SE.sel_of (vp0 x) m === SE.sel_of (vp x) m))

val elim_vp
  (#opened: _)
  (#base: Type)
  (#ap: AP.t base byte)
  (x: t ap)
: SEA.SteelGhost (squash (Steel.C.Ref.ptr_is_null x == false))
                 opened
    (vp x)
    (fun _ -> AP.varrayptr ap `SE.star` R.pts_to_view x (Steel.C.Opt.opt_view SZ.size_t))
    (requires (fun _ -> True))
    (ensures (fun h _ h' ->
      let ar = h (vp x) in
      ar == (h' (AP.varrayptr ap)).AP.array /\
      AP.len ar  == h' (R.pts_to_view x (Steel.C.Opt.opt_view SZ.size_t))
    ))

let elim_vp #_ #_ #ap x =
  SEA.change_slprop_rel
    (vp x)
    (vp0 x)
    (fun u v -> u == v)
    (fun m -> 
      assert_norm (SE.hp_of (vp0 x) == SE.hp_of (vp x));
      assert_norm (SE.sel_of (vp0 x) m === SE.sel_of (vp x) m));
  SEA.elim_vrewrite
    (SE.emp `SE.vrefine` vp_refine1 x `SE.vdep` vp_dep x)
    (vp_rewrite x);
  let g = SEA.elim_vdep
    (SE.emp `SE.vrefine` vp_refine1 x)
    (vp_dep x)
  in
  SEA.elim_vrefine SE.emp (vp_refine1 x);
  SEA.elim_vrefine (R.pts_to_view x (Steel.C.Opt.opt_view SZ.size_t) `SE.star` AP.varrayptr ap) (vp_refine2 x g)

let len x =
  elim_vp x;
  let res = R.ref_read x in
  intro_vp x ();
  SEA.return res

let split #_ #ap x ar_len =
  let ap_len = len x in
  let al_len = ap_len `SZ.size_sub` ar_len in
  elim_vp x;
  let ar = AP.split ap al_len in
  Steel.C.Opt.opt_write_sel x al_len;
  intro_vp x ();
  SEA.return ar

let merge #_ #ap x ar ar_len =
  let al_len = len x in
  elim_vp x;
  AP.join ap ar;
  let ap_len = al_len `SZ.size_add` ar_len in // MUST be done AFTER join, because of the no-overflow proof
  Steel.C.Opt.opt_write_sel x ap_len;
  intro_vp x ()
