module LowParse.SteelST.Recursive.Base
include LowParse.Spec.Recursive
include LowParse.SteelST.Access
open Steel.ST.Util
module SZ = FStar.SizeT
module R = Steel.ST.Reference

inline_for_extraction
let read_replace
  (#t: Type)
  (#p: perm)
  (#v: Ghost.erased t)
  (r: R.ref t)
: ST t
    (R.pts_to r p v)
    (fun v' ->  R.pts_to r p v')
    True
    (fun v' ->  Ghost.reveal v == v')
= let v' = R.read r in
  vpattern_rewrite (R.pts_to r _) v';
  return v'

let mul_pos_gt
  (n1: nat)
  (n2: pos)
: Lemma
  (n1 `Prims.op_Multiply` n2 >= n1)
= ()

inline_for_extraction
let jump_recursive_step_count
  (p: parse_recursive_param)
: Tot Type
=
    (#va: v p.parse_header_kind p.header) ->
    (a: byte_array) ->
    (bound: Ghost.erased SZ.t) ->
    ST SZ.t
      (aparse p.parse_header a va)
      (fun res -> aparse p.parse_header a va)
      (p.count va.contents <= SZ.v bound)
      (fun res ->
        SZ.v res == p.count va.contents
      )
