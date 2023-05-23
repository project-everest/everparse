module LowParse.SteelST.VCList.Iterator
include LowParse.SteelST.VCList
open Steel.ST.Util
module AP = LowParse.SteelST.ArrayPtr

val nlist_iterator
  (#k: parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (n: nat)
  (va: v (parse_nlist_kind n k) (nlist n t))
: Tot vprop

val nlist_iterator_parser_kind
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (n: nat)
  (va: v (parse_nlist_kind n k) (nlist n t))
: STGhost unit opened
    (nlist_iterator p n0 va0 a0 n va)
    (fun _ -> nlist_iterator p n0 va0 a0 n va)
    True
    (fun _ ->
      k.parser_kind_subkind == Some ParserStrong
    )

val nlist_iterator_begin
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#n0: nat)
  (#va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
: STGhost (v (parse_nlist_kind n0 k) (nlist n0 t)) opened
    (aparse (parse_nlist n0 p) a0 va0)
    (fun va ->
      aparse (parse_nlist n0 p) a0 va `star`
      nlist_iterator p n0 va0 a0 n0 va
    )
    (k.parser_kind_subkind == Some ParserStrong)
    (fun va ->
      va0.contents == va.contents
    )

val nlist_iterator_end
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#n0: nat)
  (#va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (#n: nat)
  (#va: v (parse_nlist_kind n k) (nlist n t))
  (a0: byte_array)
  (a: byte_array)
: STGhostT unit opened
    (nlist_iterator p n0 va0 a0 n va `star`
      aparse (parse_nlist n p) a va)
    (fun _ ->
      aparse (parse_nlist n0 p) a0 va0)

val nlist_iterator_append
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#n0: nat)
  (#va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (#n: nat)
  (#va: v (parse_nlist_kind n k) (nlist n t))
  (#n1: nat)
  (#va1: v (parse_nlist_kind n1 k) (nlist n1 t))
  (a0: byte_array)
  (a1: byte_array)
  (#n2: nat)
  (va2: v (parse_nlist_kind n2 k) (nlist n2 t))
: STGhost unit opened
    (nlist_iterator p n0 va0 a0 n va `star`
      aparse (parse_nlist n1 p) a1 va1)
    (fun _ ->
      nlist_iterator p n0 va0 a0 n2 va2)
    (AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents `List.Tot.append` va2.contents
    )
    (fun _ -> True)

val nlist_iterator_next
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#n0: nat)
  (#va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (#n: nat)
  (#va: v (parse_nlist_kind n k) (nlist n t))
  (#va1: v k t)
  (a0: byte_array)
  (a1: byte_array)
  (#n2: nat)
  (va2: v (parse_nlist_kind n2 k) (nlist n2 t))
: STGhost unit opened
    (nlist_iterator p n0 va0 a0 n va `star`
      aparse p a1 va1)
    (fun _ ->
      nlist_iterator p n0 va0 a0 n2 va2)
    (AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents :: va2.contents
    )
    (fun _ -> True)
