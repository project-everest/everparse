module LowParse.SteelST.List.Iter.ReadOnly

open LowParse.SteelST.List.Iter.ConsumesWithArray
open Steel.ST.GenElim

[@@__reduce__]
let list_iter_state0
  (#k: _)
  (#t: _)
  (p: parser k t)
  (#t': Type)
  (state: t' -> list t -> vprop)
  (a0: byte_array)
  (al: AP.array byte)
  (accu: t')
  (l: list t)
: Tot vprop
= exists_ (fun (wl: v parse_list_kind (list t)) ->
    aparse (parse_list p) a0 wl `star`
    state accu l `star` pure (
    array_of' wl == al /\
    wl.contents == l
  ))

let list_iter_state
  (#k: _)
  (#t: _)
  (p: parser k t)
  (#t': Type)
  (state: t' -> list t -> vprop)
  (a0: byte_array)
  (al: AP.array byte)
  (accu: t')
  (l: list t)
: Tot vprop
= list_iter_state0 p state a0 al accu l

#push-options "--z3rlimit 24"

inline_for_extraction
let list_iter
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
      (fun res -> aparse p a va `star` state res (List.Tot.snoc (Ghost.reveal l, va.contents)) `star` pure (res == Ghost.reveal phi accu va.contents))
  ))
  (#va: v parse_list_kind (list t))
  (a: byte_array)
  (len: SZ.size_t)
  (init: t')
: ST t'
    (aparse (parse_list p) a va `star` state init [])
    (fun res -> aparse (parse_list p) a va `star` state res va.contents)
    (SZ.size_v len == AP.length (array_of va) /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> res == List.Tot.fold_left (Ghost.reveal phi) init va.contents)
= list_split_nil_l p a;
  let _ = gen_elim () in
  let wl0 = vpattern_replace (fun wl -> aparse (parse_list p) a wl) in
  rewrite (list_iter_state0 p state a (array_of' wl0) init [])
    (list_iter_state p state a (array_of' wl0) init []);
  let wr0 = vpattern_replace (fun wr -> aparse_list p a wr) in
  let res = list_iter_consumes_with_array
    j phi
    (list_iter_state p state a)
    (fun va' a' al accu l ->
      rewrite (list_iter_state p state a al accu l) (list_iter_state0 p state a al accu l);
      let _ = gen_elim () in
      let res = f _ a' accu l in
      let _ = gen_elim () in
      let _ = intro_singleton p a' in
      let wl' = list_append p a a' in
      rewrite
        (list_iter_state0 p state a (array_of' wl') res (List.Tot.snoc (Ghost.reveal l, va'.contents)))
        (list_iter_state p state a (array_of' wl') res (List.Tot.snoc (Ghost.reveal l, va'.contents)));
      return res
    )
    a len (array_of' wl0) init
  in
  let _ = gen_elim () in
  let al' = vpattern_replace (fun al' -> list_iter_state _ _ _ al' _ _) in
  rewrite (list_iter_state p state a al' res wr0.contents) (list_iter_state0 p state a al' res wr0.contents);
  let _ = gen_elim () in
  rewrite (aparse (parse_list p) a _) (aparse (parse_list p) a va);
  rewrite (state _ _) (state res va.contents);
  return res

#pop-options

inline_for_extraction
let list_iter_opt
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
      (fun res -> aparse p a va `star` state res (List.Tot.snoc (Ghost.reveal l, va.contents)) `star` pure (res == Ghost.reveal phi accu va.contents))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.size_t)
  (init: t')
: ST t'
    (aparse_list p a va `star` state init [])
    (fun res -> aparse_list p a va `star` state res va.contents)
    (SZ.size_v len == length_opt va.array /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> res == List.Tot.fold_left (Ghost.reveal phi) init va.contents)
= let _ = ghost_is_cons_opt p a in
  if len = SZ.zero_size
  then begin
    rewrite (state _ _) (state init va.contents);
    return init
  end else begin
    let _ = elim_aparse_list_cons p a _ in
    let res = list_iter j phi state f a len init in
    let _ = intro_aparse_list_cons p a _ in
    rewrite (aparse_list _ _ _) (aparse_list p a va);
    rewrite (state _ _) (state res va.contents);
    return res
  end
