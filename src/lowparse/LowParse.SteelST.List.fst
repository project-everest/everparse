module LowParse.SteelST.List
include LowParse.SteelST.List.Iter.Gen
include LowParse.SteelST.List.Iter.ConsumesWithArray
include LowParse.SteelST.List.Iter.ReadOnly
include LowParse.SteelST.List.Iter.WithInterrupt
include LowParse.SteelST.List.Map
include LowParse.SteelST.List.Length

(*
inline_for_extraction
let list_iter_consumes
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#t': Type)
  (phi: Ghost.erased (t' -> t -> t'))
  (state: t' -> list t -> vprop)
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (accu: t') ->
    (l: Ghost.erased (list t)) ->
    STT t'
      (aparse p a va `star` state accu l)
      (fun res -> state res (List.Tot.snoc (Ghost.reveal l, va.contents)) `star` pure (res == Ghost.reveal phi accu va.contents))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.size_t)
  (init: t')
: ST t'
    (aparse_list p a va `star` state init [])
    (fun res -> state res va.contents)
    (SZ.size_v len == length_opt va.array /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> res == List.Tot.fold_left (Ghost.reveal phi) init va.contents)
= let state0 _ = state in
  rewrite (state init []) (state0 None init []);
  let res = list_iter_gen j phi false state0
    (fun _ a al accu l ->
      rewrite (state0 _ accu l) (state accu l);
      let res = f _ a accu l in
      let _ = gen_elim () in
      let l' = vpattern_replace_erased (fun l' -> state res l') in
      rewrite (state res l') (state0 None res l');
      return res
    )
    a len None init
  in
  let _ = gen_elim () in
  rewrite (state0 _ res va.contents) (state res va.contents);
  return res
*)
