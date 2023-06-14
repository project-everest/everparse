module LowParse.SteelST.ArrayPtrSwap
include LowParse.SteelST.ArrayPtrSwap.Gen
open Steel.ST.GenElim

module SZ = FStar.SizeT
module AP = LowParse.SteelST.ArrayPtr

let arrayptr_pts_to_prop
  (#t: Type)
  (a0: AP.array t)
  (s: Ghost.erased (Seq.seq t))
  (v: AP.v t)
: Tot prop
=
      AP.array_perm a0 == full_perm /\
      AP.array_of v == a0 /\
      AP.contents_of v == Ghost.reveal s

[@@__reduce__]
let arrayptr_pts_to0
  (#t: Type)
  (a: AP.t t)
  (a0: AP.array t)
: Tot (array_pts_to_t t)
= fun s -> exists_ (fun v ->
    AP.arrayptr a v `star`
    pure (arrayptr_pts_to_prop a0 s v)
  )

let arrayptr_pts_to
  (#t: Type)
  (a: AP.t t)
  (a0: AP.array t)
: Tot (array_pts_to_t t)
= arrayptr_pts_to0 a a0

inline_for_extraction
let arrayptr_index
  (#t: Type)
  (a: AP.t t)
  (a0: AP.array t)
: Tot (array_index_t (arrayptr_pts_to a a0))
= fun s n i ->
    rewrite (arrayptr_pts_to a a0 s) (arrayptr_pts_to0 a a0 s);
    let _ = gen_elim () in
    let res = AP.index a i in
    rewrite (arrayptr_pts_to0 a a0 s) (arrayptr_pts_to a a0 s);
    return res

inline_for_extraction
let arrayptr_upd
  (#t: Type)
  (a: AP.t t)
  (a0: AP.array t)
: Tot (array_upd_t (arrayptr_pts_to a a0))
= fun s n i x ->
    rewrite (arrayptr_pts_to a a0 s) (arrayptr_pts_to0 a a0 s);
    let _ = gen_elim () in
    let _ = AP.upd a i x in
    let s' : Ghost.erased (Seq.seq t) = Ghost.hide (Seq.upd s (SZ.v i) x) in
    rewrite (arrayptr_pts_to0 a a0 s') (arrayptr_pts_to a a0 s');
    return s'

let arrayptr_swap
  (#t: Type)
  (#v: AP.v t)
  (a: AP.t t)
  (n: SZ.t)
  (l: SZ.t)
: ST (AP.v t)
    (AP.arrayptr a v)
    (fun v' -> AP.arrayptr a v')
    (
      let s0 = AP.contents_of v in
      let a0 = AP.array_of v in
      AP.array_perm a0 == full_perm /\
      SZ.v n == AP.length a0 /\
      SZ.v l <= SZ.v n
    )
    (fun v' ->
      let s0 = AP.contents_of v in
      SZ.v n == Seq.length s0 /\
      SZ.v l <= SZ.v n /\
      AP.array_of v' == AP.array_of v /\
      AP.contents_of v' == Seq.slice s0 (SZ.v l) (SZ.v n) `Seq.append` Seq.slice s0 0 (SZ.v l)
    )
= let s0 : Ghost.erased (Seq.seq t) = Ghost.hide (AP.contents_of v) in
  let a0 : AP.array t = AP.array_of v in
  noop ();
  rewrite (arrayptr_pts_to0 a a0 s0) (arrayptr_pts_to a a0 s0);
  let s = array_swap_gen (arrayptr_index a a0) (arrayptr_upd a a0) s0 n l in
  rewrite (arrayptr_pts_to a a0 s) (arrayptr_pts_to0 a a0 s);
  let _ = gen_elim () in
  return _
