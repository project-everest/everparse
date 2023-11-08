module LowParse.SteelST.List.Iterator
include LowParse.SteelST.List.Base
include LowParse.SteelST.Parse
open Steel.ST.Util

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module R = Steel.ST.Reference

val list_iterator_strong
  (#k: parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (l: list t) // the list of already processed elements
  (va: v parse_list_kind (list t))
: Tot vprop

val list_iterator_strong_facts
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (l: list t)
  (va: v parse_list_kind (list t))
: STGhost unit opened
    (list_iterator_strong p va0 a0 l va)
    (fun _ -> list_iterator_strong p va0 a0 l va)
    True
    (fun _ ->
      k.parser_kind_subkind == Some ParserStrong /\
      va0.contents == l `List.Tot.append` va.contents
    )

val list_iterator
  (#k: parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (va: v parse_list_kind (list t))
: Tot vprop

val list_iterator_of_list_iterator_strong
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (l: list t)
  (va: v parse_list_kind (list t))
: STGhostT unit opened
    (list_iterator_strong p va0 a0 l va)
    (fun _ -> list_iterator p va0 a0 va)

val list_iterator_strong_of_list_iterator
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (va: v parse_list_kind (list t))
: STGhostT (Ghost.erased (list t)) opened
    (list_iterator p va0 a0 va)
    (fun l -> list_iterator_strong p va0 a0 l va)

let list_iterator_parser_kind
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va0: v parse_list_kind (list t))
  (a0: byte_array)
  (va: v parse_list_kind (list t))
: STGhost unit opened
    (list_iterator p va0 a0 va)
    (fun _ -> list_iterator p va0 a0 va)
    True
    (fun _ ->
      k.parser_kind_subkind == Some ParserStrong
    )
= let _ = list_iterator_strong_of_list_iterator _ _ _ _ in
  list_iterator_strong_facts _ _ _ _ _;
  list_iterator_of_list_iterator_strong _ _ _ _ _

val list_iterator_strong_begin
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: v parse_list_kind (list t))
  (a0: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_list p) a0 va0)
    (fun va ->
      aparse (parse_list p) a0 va `star`
      list_iterator_strong p va0 a0 [] va
    )
    (k.parser_kind_subkind == Some ParserStrong)
    (fun va -> va0.contents == va.contents /\
      AP.length (array_of' va0) == AP.length (array_of va)
    )

let list_iterator_begin
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: v parse_list_kind (list t))
  (a0: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_list p) a0 va0)
    (fun va ->
      aparse (parse_list p) a0 va `star`
      list_iterator p va0 a0 va
    )
    (k.parser_kind_subkind == Some ParserStrong)
    (fun va -> va0.contents == va.contents /\
      AP.length (array_of' va0) == AP.length (array_of va)
    )
= let va = list_iterator_strong_begin p a0 in
  list_iterator_of_list_iterator_strong _ _ _ _ _;
  va

val list_iterator_strong_end
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: v parse_list_kind (list t))
  (#va: v parse_list_kind (list t))
  (a0: byte_array)
  (l: list t)
  (a: byte_array)
: STGhostT unit opened
    (list_iterator_strong p va0 a0 l va `star`
      aparse (parse_list p) a va)
    (fun _ ->
      aparse (parse_list p) a0 va0)

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
= let _ = list_iterator_strong_of_list_iterator _ _ _ _ in
  list_iterator_strong_end _ _ _ _

val list_iterator_strong_append
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: v parse_list_kind (list t))
  (#va: v parse_list_kind (list t))
  (#va1: v parse_list_kind (list t))
  (a0: byte_array)
  (l: list t)
  (a1: byte_array)
  (va2: v parse_list_kind (list t))
: STGhost unit opened
    (list_iterator_strong p va0 a0 l va `star`
      aparse (parse_list p) a1 va1)
    (fun a ->
      list_iterator_strong p va0 a0 (l `List.Tot.append` va1.contents) va2)
    (AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents `List.Tot.append` va2.contents
    )
    (fun _ -> True)

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
= let _ = list_iterator_strong_of_list_iterator _ _ _ _ in
  list_iterator_strong_append _ _ _ _ _;
  list_iterator_of_list_iterator_strong _ _ _ _ _

val list_iterator_strong_next
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: v parse_list_kind (list t))
  (#va: v parse_list_kind (list t))
  (#va1: v k t)
  (a0: byte_array)
  (l: list t)
  (a1: byte_array)
  (va2: v parse_list_kind (list t))
: STGhost unit opened
    (list_iterator_strong p va0 a0 l va `star`
      aparse p a1 va1)
    (fun a ->
      list_iterator_strong p va0 a0 (l `List.Tot.append` [va1.contents]) va2)
    (AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      AP.length (array_of va1) > 0 /\
      va.contents == va1.contents :: va2.contents
    )
    (fun _ -> True)

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
      AP.length (array_of va1) > 0 /\
      va.contents == va1.contents :: va2.contents
    )
    (fun _ -> True)
= let _ = list_iterator_strong_of_list_iterator _ _ _ _ in
  list_iterator_strong_next _ _ _ _ _;
  list_iterator_of_list_iterator_strong _ _ _ _ _

val list_slice
  (#k: parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (psz: R.ref SZ.t)
  (a: byte_array)
  (va: v parse_list_kind (list t))
: Tot vprop

val intro_list_slice
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

val elim_list_slice
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
