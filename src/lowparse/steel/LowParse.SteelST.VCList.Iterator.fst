module LowParse.SteelST.VCList.Iterator
include LowParse.SteelST.VCList
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr

let nlist_iterator_prop
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (n: nat)
  (va: v (parse_nlist_kind n k) (nlist n t))
  (nl: nat)
  (vl: v (parse_nlist_kind nl k) (nlist nl t))
: GTot prop
=
      k.parser_kind_subkind == Some ParserStrong /\
      AP.merge_into (array_of vl) (array_of va) (array_of va0) /\
      va0.contents == List.Tot.append vl.contents va.contents /\
      n0 == nl + n

[@@__reduce__]
let nlist_iterator0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (n: nat)
  (va: v (parse_nlist_kind n k) (nlist n t))
: Tot vprop
= exists_ (fun (nl: nat) -> exists_ (fun (vl: v (parse_nlist_kind nl k) (nlist nl t))  ->
    aparse (parse_nlist nl p) a0 vl `star`
    pure (nlist_iterator_prop p n0 va0 a0 n va nl vl)
  ))

let nlist_iterator
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (n: nat)
  (va: v (parse_nlist_kind n k) (nlist n t))
: Tot vprop
= nlist_iterator0 p n0 va0 a0 n va

#set-options "--ide_id_info_off"

let nlist_iterator_parser_kind
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
= rewrite
    (nlist_iterator p n0 va0 a0 n va)
    (nlist_iterator0 p n0 va0 a0 n va);
  let _ = gen_elim () in
  noop ();
  rewrite
    (nlist_iterator0 p n0 va0 a0 n va)
    (nlist_iterator p n0 va0 a0 n va)

let nlist_iterator_begin
  #_ #k #t p #n0 #va0 a0
= let _ = elim_aparse (parse_nlist n0 p) a0 in
  let a = AP.gsplit a0 0sz in
  let _ = gen_elim () in
  let _ = intro_nlist_nil (n0 - n0) p a0 in
  vpattern_rewrite (fun a -> AP.arrayptr a _) a0;
  let va = intro_aparse (parse_nlist n0 p) a0 in
  rewrite
    (nlist_iterator0 p n0 va0 a0 n0 va)
    (nlist_iterator p n0 va0 a0 n0 va);
  _

#push-options "--z3rlimit 16"

let nlist_iterator_end
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
= rewrite
    (nlist_iterator p n0 va0 a0 n va)
    (nlist_iterator0 p n0 va0 a0 n va);
  let _ = gen_elim () in
  let _ = intro_nlist_sum n0 p _ a0 n a in
  vpattern_rewrite (aparse _ _) va0

#restart-solver
let nlist_iterator_append
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
= List.Tot.append_length va1.contents va2.contents;
  noop ();
  rewrite
    (nlist_iterator p n0 va0 a0 n va)
    (nlist_iterator0 p n0 va0 a0 n va);
  let _ = gen_elim () in
  let vl = rewrite_aparse a0 (parse_nlist (n0 - n) p) in
  List.Tot.append_assoc vl.contents va1.contents va2.contents;
  noop ();
  let _ = intro_nlist_sum (n0 - n2) p (n0 - n) a0 n1 a1 in
  rewrite
    (nlist_iterator0 p n0 va0 a0 n2 va2)
    (nlist_iterator p n0 va0 a0 n2 va2)

#pop-options

let nlist_iterator_next
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
= nlist_iterator_parser_kind p n0 va0 a0 n va;
  let _ = intro_nlist_one p a1 1 in
  nlist_iterator_append p a0 a1 va2
