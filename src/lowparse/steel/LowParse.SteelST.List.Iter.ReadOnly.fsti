module LowParse.SteelST.List.Iter.ReadOnly
include LowParse.SteelST.List.Base

open Steel.ST.Util

module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT

inline_for_extraction
val list_iter
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#t': Type0)
  (phi: Ghost.erased (t' -> t -> t'))
  (state: t' -> list t -> vprop)
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (accu: t') ->
    (l: Ghost.erased (list t)) ->
    STT t'
      (aparse p a va `star` state accu l)
      (fun res -> aparse p a va `star` state res (List.Tot.snoc (Ghost.reveal l, va.contents)) `star` pure (res == Ghost.reveal phi accu va.contents))
  ))
  (#va: v parse_list_kind (list t))
  (a: byte_array)
  (len: SZ.t)
  (init: t')
: ST t'
    (aparse (parse_list p) a va `star` state init [])
    (fun res -> aparse (parse_list p) a va `star` state res va.contents)
    (SZ.v len == AP.length (array_of va) /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> res == List.Tot.fold_left (Ghost.reveal phi) init va.contents)

inline_for_extraction
val list_iter_opt
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#t': Type0)
  (phi: Ghost.erased (t' -> t -> t'))
  (state: t' -> list t -> vprop)
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (accu: t') ->
    (l: Ghost.erased (list t)) ->
    STT t'
      (aparse p a va `star` state accu l)
      (fun res -> aparse p a va `star` state res (List.Tot.snoc (Ghost.reveal l, va.contents)) `star` pure (res == Ghost.reveal phi accu va.contents))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.t)
  (init: t')
: ST t'
    (aparse_list p a va `star` state init [])
    (fun res -> aparse_list p a va `star` state res va.contents)
    (SZ.v len == length_opt va.array /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> res == List.Tot.fold_left (Ghost.reveal phi) init va.contents)
