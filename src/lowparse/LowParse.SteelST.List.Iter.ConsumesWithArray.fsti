module LowParse.SteelST.List.Iter.ConsumesWithArray
include LowParse.SteelST.List.Base

open Steel.ST.Util

module AP = LowParse.SteelST.ArrayPtr
module SZ = LowParse.Steel.StdInt

unfold
let list_iter_consumes_with_array_body_post0
  (k: parser_kind)
  (#t: Type)
  (#t': Type)
  (phi: Ghost.erased (t' -> t -> t'))
  (va: v k t { AP.length (array_of' va) > 0 })
  (al: AP.array byte { AP.adjacent al (array_of' va) })
  (accu: t')
  (l: Ghost.erased (list t))
  (al': AP.array byte)
  (l': list t)
  (res: t')
: Tot prop
=
  AP.merge_into al (array_of' va) al' /\
  l' == List.Tot.snoc (Ghost.reveal l, va.contents) /\
  res == Ghost.reveal phi accu va.contents

let list_iter_consumes_with_array_body_post
  (k: parser_kind)
  (#t: Type)
  (#t': Type)
  (phi: Ghost.erased (t' -> t -> t'))
  (va: v k t { AP.length (array_of' va) > 0 })
  (al: AP.array byte { AP.adjacent al (array_of' va) })
  (accu: t')
  (l: Ghost.erased (list t))
  (al': AP.array byte)
  (l': list t)
  (res: t')
: Tot prop
= list_iter_consumes_with_array_body_post0 k phi va al accu l al' l' res

let list_iter_consumes_with_array_body_post_intro
  (k: parser_kind)
  (#t: Type)
  (#t': Type)
  (phi: Ghost.erased (t' -> t -> t'))
  (va: v k t { AP.length (array_of' va) > 0 })
  (al: AP.array byte { AP.adjacent al (array_of' va) })
  (accu: t')
  (l: Ghost.erased (list t))
  (al': AP.array byte)
  (l': list t)
  (res: t')
: Lemma
  (requires (list_iter_consumes_with_array_body_post0 k phi va al accu l al' l' res))
  (ensures (list_iter_consumes_with_array_body_post k phi va al accu l al' l' res))
= ()

inline_for_extraction
val list_iter_consumes_with_array
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#t': Type0)
  (phi: Ghost.erased (t' -> t -> t'))
  (state: AP.array byte -> t' -> list t -> vprop)
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (al: AP.array byte { AP.adjacent al (array_of' va) } ) ->
    (accu: t') ->
    (l: Ghost.erased (list t)) ->
    STT t'
      (aparse p a va `star` state al accu l)
      (fun res -> exists_ (fun al' -> exists_ (fun l' -> state al' res l' `star` pure (
        list_iter_consumes_with_array_body_post k phi va al accu l al' l' res
  ))))))
  (#va: _)
  (a: byte_array)
  (len: SZ.size_t)
  (al: AP.array byte)
  (init: t')
: ST t'
    (aparse_list p a va `star` state al init [])
    (fun res -> exists_ (fun al' ->
      state al' res va.contents `star` pure (
      merge_opt_into al va.array al' /\
      res == List.Tot.fold_left (Ghost.reveal phi) init va.contents      
    )))
    (SZ.size_v len == length_opt va.array /\
      k.parser_kind_subkind == Some ParserStrong /\
      adjacent_opt al va.array
    )
    (fun res -> True)
