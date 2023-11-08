module LowParse.SteelST.List.Iter.WithInterrupt
include LowParse.SteelST.List.Base

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

open Steel.ST.Util

inline_for_extraction
val list_iter_with_interrupt
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (state: bool -> list t -> vprop)
  (f_true: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (l: Ghost.erased (list t)) ->
    STT bool
      (aparse p a va `star` state true l)
      (fun res -> aparse p a va `star` state res (List.Tot.snoc (Ghost.reveal l, va.contents)))
  ))
  (f_false: (
    (#opened: _) ->
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (l: Ghost.erased (list t)) ->
    STGhostT unit opened
      (aparse p a va `star` state false l)
      (fun res -> aparse p a va `star` state false (List.Tot.snoc (Ghost.reveal l, va.contents)))
  ))  
  (#v0: v parse_list_kind (list t))
  (bin: byte_array)
  (len: SZ.t)
: ST bool
    (aparse (parse_list p) bin v0 `star` state true [])
    (fun res -> aparse (parse_list p) bin v0 `star` state res v0.contents)
    (SZ.v len == AP.length (array_of v0) /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
