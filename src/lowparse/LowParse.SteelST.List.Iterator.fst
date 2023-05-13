module LowParse.SteelST.List.Iterator
open Steel.ST.GenElim

let list_iterator_strong_prop
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (l: list t)
  (va: v parse_list_kind (list t))
  (vl: v parse_list_kind (list t))
: GTot prop
=
      k.parser_kind_subkind == Some ParserStrong /\
      AP.merge_into (array_of vl) (array_of va) (array_of va0) /\
      l == vl.contents /\
      va0.contents == List.Tot.append vl.contents va.contents

[@@__reduce__]
let list_iterator_strong0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (l: list t)
  (va: v parse_list_kind (list t))
: Tot vprop
= exists_ (fun vl ->
    aparse (parse_list p) a0 vl `star`
    pure (list_iterator_strong_prop p va0 a0 l va vl)
  )

let list_iterator_strong
  p va0 a0 l va
= list_iterator_strong0 p va0 a0 l va

let list_iterator_strong_facts
  p va0 a0 l va
= rewrite
    (list_iterator_strong p va0 a0 l va)
    (list_iterator_strong0 p va0 a0 l va);
  let _ = gen_elim () in
  noop ();
  rewrite
    (list_iterator_strong0 p va0 a0 l va)
    (list_iterator_strong p va0 a0 l va)

[@@__reduce__]
let list_iterator0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (va: v parse_list_kind (list t))
: Tot vprop
= exists_ (fun l ->
    list_iterator_strong p va0 a0 l va
  )

let list_iterator
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (va: v parse_list_kind (list t))
: Tot vprop
= list_iterator0 p va0 a0 va

let list_iterator_of_list_iterator_strong
  p va0 a0 l va
= noop ();
  rewrite
    (list_iterator0 p va0 a0 va)
    (list_iterator p va0 a0 va)

let list_iterator_strong_of_list_iterator
  p va0 a0 va
= elim_exists ()

let list_iterator_strong_begin
  p #va0 a0
= let _ = elim_aparse (parse_list p) a0 in
  let a = AP.gsplit a0 0sz in
  let _ = gen_elim () in
  let _ = intro_nil p a0 in
  let va = intro_aparse (parse_list p) a in
  rewrite (aparse _ a _) (aparse (parse_list p) a0 va);
  rewrite
    (list_iterator_strong0 p va0 a0 [] va)
    (list_iterator_strong p va0 a0 [] va);
  va

let list_iterator_strong_end
  p #va0 #va a0 l a
= rewrite
    (list_iterator_strong p va0 a0 l va)
    (list_iterator_strong0 p va0 a0 l va);
  let _ = gen_elim () in
  let _ = list_append p a0 a in
  vpattern_rewrite (aparse _ _) va0

let list_iterator_strong_append
  p #va0 #va #va1 a0 l a1 va2
= rewrite
    (list_iterator_strong p va0 a0 l va)
    (list_iterator_strong0 p va0 a0 l va);
  let _ = gen_elim () in
  let va = vpattern_replace (aparse _ a0) in
  List.Tot.append_assoc va.contents va1.contents va2.contents;
  noop ();
  let _ = list_append p a0 a1 in
  rewrite
    (list_iterator_strong0 p va0 a0 (l `List.Tot.append` va1.contents) va2)
    (list_iterator_strong p va0 a0 (l `List.Tot.append` va1.contents) va2)

let list_iterator_strong_next
  p #va0 #va #va1 a0 l a1 va2
= list_iterator_strong_facts p va0 a0 l va;
  let _ = intro_singleton p a1 in
  list_iterator_strong_append p a0 l a1 va2;
  vpattern_rewrite (fun l -> list_iterator_strong _ _ _ l _) (l `List.Tot.append` [va1.contents])

[@@__reduce__]
let list_slice0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (psz: R.ref SZ.t)
  (a: byte_array)
  (va: v parse_list_kind (list t))
: Tot vprop
= aparse (parse_list p) a va `star`
  R.pts_to psz full_perm (AP.len (array_of va)) `star`
  pure (
    k.parser_kind_subkind == Some ParserStrong
  )

let list_slice
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (psz: R.ref SZ.t)
  (a: byte_array)
  (va: v parse_list_kind (list t))
: Tot vprop
= list_slice0 p psz a va

let intro_list_slice
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#sz: SZ.t)
  (psz: R.ref SZ.t)
  (#va: v parse_list_kind (list t))
  (a: byte_array)
: STGhost unit opened
    (aparse (parse_list p) a va `star`
      R.pts_to psz full_perm sz)
    (fun _ -> list_slice p psz a va)
    (k.parser_kind_subkind == Some ParserStrong /\
      SZ.v sz == AP.length (array_of va))
    (fun _ -> True)
= noop ();
  rewrite (list_slice0 p psz a va) (list_slice p psz a va)

let elim_list_slice
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (psz: R.ref SZ.t)
  (#va: v parse_list_kind (list t))
  (a: byte_array)
: STGhost unit opened
    (list_slice p psz a va)
    (fun _ -> aparse (parse_list p) a va `star`
      R.pts_to psz full_perm (AP.len (array_of va)))
    True
    (fun _ -> k.parser_kind_subkind == Some ParserStrong
    )
= rewrite (list_slice p psz a va) (list_slice0 p psz a va);
  let _ = gen_elim () in
  noop ()

