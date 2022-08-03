module LowParse.SteelST.List.Iter.Gen
include LowParse.SteelST.List.Base

module AP = LowParse.SteelST.ArrayPtr
module P = Steel.FractionalPermission
module SZ = LowParse.Steel.StdInt

open Steel.ST.Util

inline_for_extraction
val list_iter_gen
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#t': Type0)
  (phi: Ghost.erased (t' -> t -> t'))
  (enable_arrays: Ghost.erased bool)
  (state: option (AP.array byte) -> t' -> list t -> vprop)
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (al: Ghost.erased (option (AP.array byte)) { (Ghost.reveal enable_arrays ==> (Some? al /\ AP.adjacent (Some?.v al) (array_of' va))) } ) ->
    (accu: t') ->
    (l: Ghost.erased (list t)) ->
    STT t'
      (aparse p a va `star` state al accu l)
      (fun res -> exists_ (fun al' -> exists_ (fun l' -> state al' res l' `star` pure (
        (Ghost.reveal enable_arrays ==> (Some? al' /\ AP.merge_into (Some?.v al) (array_of' va) (Some?.v al'))) /\
        l' == List.Tot.snoc (Ghost.reveal l, va.contents) /\
        res == Ghost.reveal phi accu va.contents
  ))))))
  (#va: _)
  (a: byte_array)
  (len: SZ.size_t)
  (al: Ghost.erased (option (AP.array byte)))
  (init: t')
: ST t'
    (aparse_list p a va `star` state al init [])
    (fun res -> exists_ (fun al' ->
      state al' res va.contents `star` pure (
      (Ghost.reveal enable_arrays ==> (Some? al /\ Some? al' /\ merge_opt_into (Some?.v al) va.array (Some?.v al'))) /\
      res == List.Tot.fold_left (Ghost.reveal phi) init va.contents      
    )))
    (SZ.size_v len == length_opt va.array /\
      k.parser_kind_subkind == Some ParserStrong /\
      (Ghost.reveal enable_arrays ==> (Some? al /\ adjacent_opt (Some?.v al) va.array))
    )
    (fun res -> True)
