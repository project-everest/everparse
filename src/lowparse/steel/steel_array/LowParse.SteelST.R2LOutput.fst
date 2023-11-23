module LowParse.SteelST.R2LOutput
open Steel.ST.GenElim

module P = Steel.ST.Reference

noeq
type t = {
  ptr: AP.t byte;
  len: P.ref SZ.t
}

[@@__reduce__]
let vp0
  (x: t)
  (vx: AP.array byte)
: Tot vprop
= exists_ (fun va ->
    AP.arrayptr x.ptr va `star`
    P.pts_to x.len full_perm (AP.len vx) `star`
    pure (
     AP.array_of va == vx /\
     AP.array_perm vx == full_perm
 ))

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
  let xlen = P.read x.len in
  let xlen' = xlen `SZ.sub` len in
  let res = AP.split x.ptr xlen' in
  let _ = gen_elim () in
  P.write x.len xlen';
  let vx' = vpattern_replace (AP.arrayptr x.ptr) in
  noop ();
  rewrite
    (vp0 x (AP.array_of vx'))
    (vp x (AP.array_of vx'));
  return res

let revert
  #vx x y len
=
  rewrite
    (vp x vx)
    (vp0 x vx);
  let _ = gen_elim () in
  let vx' = AP.join x.ptr y in
  P.write x.len len;
  noop ();
  rewrite
    (vp0 x (AP.array_of vx'))
    (vp x (AP.array_of vx'));
  return _

let hop
  #vx x y
=
  rewrite
    (vp x vx)
    (vp0 x vx);
  let _ = gen_elim () in
  let xlen = P.read x.len in
  let res = AP.split' x.ptr xlen y in
  noop ();
  rewrite
    (vp0 x vx)
    (vp x vx);
  return res
