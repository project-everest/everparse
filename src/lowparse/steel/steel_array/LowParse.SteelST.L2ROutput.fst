module LowParse.SteelST.L2ROutput
open Steel.ST.GenElim

module P = Steel.ST.Reference

noeq
type t = {
  ptr: P.ref (AP.t byte);
  len: P.ref SZ.t
}

[@@__reduce__]
let vp0
  (x: t)
  (vx: AP.array byte)
: Tot vprop
= exists_ (fun a -> exists_ (fun va ->
    AP.arrayptr a va `star`
    P.pts_to x.ptr full_perm a `star`
    P.pts_to x.len full_perm (AP.len vx) `star`
    pure (
     AP.array_of va == vx /\
     AP.array_perm vx == full_perm
 )))

let vp
  x vx
= vp0 x vx

let vp_perm
  #_ #va x
=
  rewrite
    (vp x va)
    (vp0 x va);
  let _ = gen_elim () in
  rewrite
    (vp0 x va)
    (vp x va)

let len
  #va x
=
  rewrite
    (vp x va)
    (vp0 x va);
  let _ = gen_elim () in
  let len = P.read x.len in
  rewrite
    (vp0 x va)
    (vp x va);
  return len

let split
  #va x len
=
  rewrite
    (vp x va)
    (vp0 x va);
  let _ = gen_elim () in
  let res = P.read x.ptr in
  vpattern_rewrite (fun a -> AP.arrayptr a _) res;
  let xlen = P.read x.len in
  let xlen' = xlen `SZ.sub` len in
  let xptr' = AP.split res len in
  let _ = gen_elim () in
  P.write x.ptr xptr';
  P.write x.len xlen';
  let vx' = vpattern_replace (AP.arrayptr xptr') in
  noop ();
  rewrite
    (vp0 x (AP.array_of vx'))
    (vp x (AP.array_of vx'));
  return res

let revert
  y len #vx x
=
  rewrite
    (vp x vx)
    (vp0 x vx);
  let _ = gen_elim () in
  let vx' = AP.join y _ in
  P.write x.ptr y;
  P.write x.len len;
  noop ();
  rewrite
    (vp0 x (AP.array_of vx'))
    (vp x (AP.array_of vx'));
  return _
