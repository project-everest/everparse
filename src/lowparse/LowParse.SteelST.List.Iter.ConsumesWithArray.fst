module LowParse.SteelST.List.Iter.ConsumesWithArray
open LowParse.SteelST.List.Iter.Gen
open Steel.ST.GenElim

inline_for_extraction
let list_iter_consumes_with_array
  #k #t #p j #t' phi state f #va a len al init
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
= [@inline_let]
  let state0 x = match x with None -> (fun _ _ -> pure False) | Some x' -> state x' in
  [@inline_let]
  let state0_is_some (#opened: _) al accu l : STGhost unit opened (state0 al accu l) (fun _ -> state0 al accu l) True (fun _ -> Some? al) =
    if Some? al
    then noop ()
    else begin
      rewrite (state0 al accu l) (pure False);
      let _ = gen_elim () in
      rewrite emp (state0 al accu l) // by contradiction
    end
  in
  rewrite (state al init []) (state0 (Some al) init []);
  let res = list_iter_gen j phi true state0
    (fun _ a al accu l ->
      state0_is_some al accu l;
      let al = Some?.v al in
      rewrite (state0 _ accu l) (state al accu l);
      let res = f _ a al accu l in
      let _ = gen_elim () in
      let l' = vpattern_replace_erased (fun l' -> state _ _ l') in
      let al' = vpattern_replace (fun al' -> state al' _ _) in
      rewrite (state al' res l') (state0 (Some al') res l');
      return res
    )
    a len (Some al) init
  in
  let _ = gen_elim () in
  state0_is_some _ _ _;
  let al' = vpattern_replace_erased (fun al' -> state0 al' _ _) in
  rewrite (state0 _ _ _) (state (Some?.v al') res va.contents);
  return res
