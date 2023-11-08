module LowParse.SteelST.L2ROutput.IntroElim
friend LowParse.SteelST.L2ROutput
open Steel.ST.GenElim

[@@__reduce__]
let is_l2r_output_buffer
  a sz res
= pure (
    res.ptr == a /\
    res.len == sz
  )

let intro_vp
  #vsz #va #a pa sz
= [@@inline_let]
  let res = {
    ptr = pa;
    len = sz;
  }
  in
  noop ();
  vpattern_rewrite
    (fun pa -> R.pts_to #(AP.t byte) pa _ _)
    res.ptr;
  vpattern_rewrite
    (fun sz -> R.pts_to #SZ.t sz _ _)
    res.len;
  rewrite
    (vp0 res (AP.array_of va))
    (vp res (AP.array_of va));
  return res

let elim_vp
  #pa #sz #va' a'
= rewrite
    (vp a' va')
    (vp0 a' va');
  let _ = gen_elim () in
  let res = R.read a'.ptr in
  vpattern_rewrite
    (fun a -> AP.arrayptr a _)
    res;
  rewrite
    (R.pts_to a'.ptr _ _)
    (R.pts_to pa full_perm res);
  rewrite
    (R.pts_to a'.len _ _)
    (R.pts_to sz full_perm (AP.len va'));
  return res
