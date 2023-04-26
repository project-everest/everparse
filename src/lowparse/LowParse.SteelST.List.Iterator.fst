module LowParse.SteelST.List.Iterator
include LowParse.SteelST.List.Base
include LowParse.SteelST.Parse
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr

let list_iterator_prop
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (va: v parse_list_kind (list t))
  (vl: v parse_list_kind (list t))
: GTot prop
=
      k.parser_kind_subkind == Some ParserStrong /\
      k.parser_kind_low > 0 /\
      AP.merge_into (array_of vl) (array_of va) (array_of va0) /\
      va0.contents == List.Tot.append vl.contents va.contents

[@@__reduce__]
let list_iterator0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (va: v parse_list_kind (list t))
: Tot vprop
= exists_ (fun vl ->
    aparse (parse_list p) a0 vl `star`
    pure (list_iterator_prop p va0 a0 va vl)
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

let list_iterator_parser_kind
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (va: v parse_list_kind (list t))
: STGhost unit opened
    (list_iterator p va0 a0 va)
    (fun _ -> list_iterator p va0 a0 va)
    True
    (fun _ ->
      k.parser_kind_subkind == Some ParserStrong /\
      k.parser_kind_low > 0
    )
= rewrite
    (list_iterator p va0 a0 va)
    (list_iterator0 p va0 a0 va);
  let _ = gen_elim () in
  noop ();
  rewrite
    (list_iterator0 p va0 a0 va)
    (list_iterator p va0 a0 va)

inline_for_extraction
let list_iterator_begin
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: v parse_list_kind (list t))
  (a0: byte_array)
: ST byte_array
    (aparse (parse_list p) a0 va0)
    (fun a -> exists_ (fun va ->
      aparse (parse_list p) a va `star`
      list_iterator p va0 a0 va `star`
      pure (
        va0.contents == va.contents
      )
    ))
    (k.parser_kind_subkind == Some ParserStrong /\
      k.parser_kind_low > 0)
    (fun _ -> True)
= let _ = elim_aparse (parse_list p) a0 in
  let a = AP.split a0 0sz in
  let _ = gen_elim () in
  let _ = intro_nil p a0 in
  let va = intro_aparse (parse_list p) a in
  rewrite
    (list_iterator0 p va0 a0 va)
    (list_iterator p va0 a0 va);
  return a

inline_for_extraction
let list_iterator_end
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: v parse_list_kind (list t))
  (#va: v parse_list_kind (list t))
  (a0: byte_array)
  (a: byte_array)
: STGhostT unit opened
    (list_iterator p va0 a0 va `star`
      aparse (parse_list p) a va)
    (fun _ ->
      aparse (parse_list p) a0 va0)
= rewrite
    (list_iterator p va0 a0 va)
    (list_iterator0 p va0 a0 va);
  let _ = gen_elim () in
  let _ = list_append p a0 a in
  vpattern_rewrite (aparse _ _) va0

inline_for_extraction
let list_iterator_append
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: v parse_list_kind (list t))
  (#va: v parse_list_kind (list t))
  (#va1: v parse_list_kind (list t))
  (a0: byte_array)
  (a1: byte_array)
  (va2: v parse_list_kind (list t))
: STGhost unit opened
    (list_iterator p va0 a0 va `star`
      aparse (parse_list p) a1 va1)
    (fun a ->
      list_iterator p va0 a0 va2)
    (AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents `List.Tot.append` va2.contents
    )
    (fun _ -> True)
= rewrite
    (list_iterator p va0 a0 va)
    (list_iterator0 p va0 a0 va);
  let _ = gen_elim () in
  let va = vpattern_replace (aparse _ a0) in
  List.Tot.append_assoc va.contents va1.contents va2.contents;
  noop ();
  let _ = list_append p a0 a1 in
  rewrite
    (list_iterator0 p va0 a0 va2)
    (list_iterator p va0 a0 va2)

inline_for_extraction
let list_iterator_next
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: v parse_list_kind (list t))
  (#va: v parse_list_kind (list t))
  (#va1: v k t)
  (a0: byte_array)
  (a1: byte_array)
  (va2: v parse_list_kind (list t))
: STGhost unit opened
    (list_iterator p va0 a0 va `star`
      aparse p a1 va1)
    (fun a ->
      list_iterator p va0 a0 va2)
    (AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents :: va2.contents
    )
    (fun _ -> True)
= list_iterator_parser_kind p va0 a0 va;
  let _ = intro_singleton p a1 in
  list_iterator_append p a0 a1 va2

module SZ = FStar.SizeT
module R = Steel.ST.Reference

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
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0
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
      k.parser_kind_low > 0 /\
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
    (fun _ -> k.parser_kind_subkind == Some ParserStrong /\
      k.parser_kind_low > 0
    )
= rewrite (list_slice p psz a va) (list_slice0 p psz a va);
  let _ = gen_elim () in
  noop ()

