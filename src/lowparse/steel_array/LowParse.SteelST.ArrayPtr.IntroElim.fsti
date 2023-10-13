module LowParse.SteelST.ArrayPtr.IntroElim
open Steel.ST.GenElim
include LowParse.SteelST.ArrayPtr

module SA = Steel.ST.Array
module SZ = FStar.SizeT

val steel_array_of_array
  (#elt: Type)
  (a: array elt)
: Ghost (SA.array elt)
    (requires True)
    (ensures (fun a' -> SA.length a' == length a))

val steel_array_of_array_adjacent
  (#elt: Type)
  (a1 a2: array elt)
: Lemma
  (requires (adjacent a1 a2))
  (ensures (
    SA.adjacent (steel_array_of_array a1) (steel_array_of_array a2) /\
    steel_array_of_array (merge a1 a2) == SA.merge (steel_array_of_array a1) (steel_array_of_array a2)
  ))

val mk_array
  (#elt: Type)
  (a: SA.array elt)
  (p: perm)
: Pure (array elt)
    (requires True)
    (ensures (fun y ->
      steel_array_of_array y == a /\
      array_perm y == p
    ))

inline_for_extraction
val intro_arrayptr_with_implies
  (#elt: Type)
  (#p: perm)
  (#va: Ghost.erased (Seq.seq elt))
  (a: SA.array elt)
: STT (t elt)
  (SA.pts_to a p va)
  (fun a' -> exists_ (fun va' ->
    arrayptr a' va' `star`
    (arrayptr a' va' `implies_` SA.pts_to a p va) `star`
    pure (
      contents_of' va' == Ghost.reveal va /\
      array_of va' == mk_array a p
  )))

inline_for_extraction
let intro_arrayptr
  (#elt: Type)
  (#p: perm)
  (#va: Ghost.erased (Seq.seq elt))
  (a: SA.array elt)
: STT (t elt)
  (SA.pts_to a p va)
  (fun a' -> exists_ (fun va' ->
    arrayptr a' va' `star`
    pure (
      contents_of' va' == Ghost.reveal va /\
      array_of va' == mk_array a p
  )))
= let a' = intro_arrayptr_with_implies a in
  let _ = gen_elim () in
  drop (arrayptr _ _ `implies_` SA.pts_to _ _ _);
  return a'

inline_for_extraction
val elim_arrayptr_with_implies
  (#elt: Type)
  (#va: v elt)
  (a: t elt)
: ST (SA.array elt)
    (arrayptr a va)
    (fun a' ->
      SA.pts_to a' (array_perm (array_of va)) (contents_of' va) `star`
        (SA.pts_to a' (array_perm (array_of va)) (contents_of' va) `implies_` arrayptr a va)
    )
    True
    (fun a' ->
      steel_array_of_array (array_of va) == a'
    )

inline_for_extraction
let elim_arrayptr
  (#elt: Type)
  (#va: v elt)
  (a: t elt)
: ST (SA.array elt)
    (arrayptr a va)
    (fun a' ->
      SA.pts_to a' (array_perm (array_of va)) (contents_of' va)
    )
    True
    (fun a' ->
      steel_array_of_array (array_of va) == a'
    )
= let a' = elim_arrayptr_with_implies a in
  let _ = gen_elim () in
  drop (SA.pts_to _ _ _ `implies_` arrayptr _ _);
  return a'
