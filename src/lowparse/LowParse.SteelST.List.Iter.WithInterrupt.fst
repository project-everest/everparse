module LowParse.SteelST.List.Iter.WithInterrupt

module R = Steel.ST.Reference

open Steel.ST.GenElim

let list_iter_with_interrupt_prop
  (#t: Type)
  (v0 vbin vcur: v parse_list_kind (list t))
  (sz: SZ.size_t)
  (cont: bool)
  (loop_cont: bool)
: Tot prop
= AP.merge_into (array_of' vbin) (array_of' vcur) (array_of' v0) /\
  v0.contents == List.Tot.append vbin.contents vcur.contents /\
  SZ.size_v sz == AP.length (array_of' vcur) /\
  loop_cont == (SZ.size_v sz > 0 && cont)

[@@__reduce__]
let list_iter_with_interrupt_inv0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (state: bool -> list t -> vprop)
  (v0: v parse_list_kind (list t))
  (bin: byte_array)
  (bcur: R.ref byte_array)
  (bsz: R.ref SZ.size_t)
  (bcont: R.ref bool)
  (bloop_cont: R.ref bool)
  (loop_cont: bool)
: Tot vprop
= exists_ (fun (vbin: v parse_list_kind (list t)) -> exists_ (fun cur -> exists_ (fun (vcur: v parse_list_kind (list t)) -> exists_ (fun sz -> exists_ (fun cont ->
    aparse (parse_list p) bin vbin `star`
    R.pts_to bcur full_perm cur `star`
    aparse (parse_list p) cur vcur `star`
    R.pts_to bsz full_perm sz `star`
    R.pts_to bcont full_perm cont `star`
    state cont vbin.contents `star`
    R.pts_to bloop_cont full_perm loop_cont `star`
    pure (
      list_iter_with_interrupt_prop v0 vbin vcur sz cont loop_cont
    )
  )))))

let list_iter_with_interrupt_inv
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (state: bool -> list t -> vprop)
  (v0: v parse_list_kind (list t))
  (bin: byte_array)
  (bcur: R.ref byte_array)
  (bsz: R.ref SZ.size_t)
  (bcont: R.ref bool)
  (bloop_cont: R.ref bool)
  (loop_cont: bool)
: Tot vprop
= list_iter_with_interrupt_inv0 p state v0 bin bcur bsz bcont bloop_cont loop_cont

#push-options "--z3rlimit 16"
#restart-solver

let rec list_iter_with_interrupt_close_false
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (state: bool -> list t -> vprop)
  (f_false: (
    (#opened: _) ->
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (l: Ghost.erased (list t)) ->
    STGhostT unit opened
      (aparse p a va `star` state false l)
      (fun res -> aparse p a va `star` state false (List.Tot.snoc (Ghost.reveal l, va.contents)))
  ))  
  (v0: v parse_list_kind (list t))
  (bin: byte_array)
  (cur: byte_array)
  (vbin: v parse_list_kind (list t))
  (vcur: v parse_list_kind (list t))
: STGhost unit opened
    (aparse (parse_list p) bin vbin `star` aparse (parse_list p) cur vcur `star` state false vbin.contents)
    (fun _ -> aparse (parse_list p) bin v0 `star` state false v0.contents)
    (
      k.parser_kind_subkind == Some ParserStrong /\
      AP.merge_into (array_of' vbin) (array_of' vcur) (array_of' v0) /\
      v0.contents == List.Tot.append vbin.contents vcur.contents
    )
    (fun _ -> True)
    (decreases vcur.contents)
= if Nil? vcur.contents
  then begin
    List.Tot.append_l_nil vbin.contents;
    let _ = list_append _ bin cur in
    rewrite (aparse _ bin _) (aparse (parse_list p) bin v0);
    rewrite (state _ _) (state false v0.contents)
  end else begin
    let cur' = ghost_elim_cons _ cur in
    let _ = gen_elim () in
    let vcur' : v parse_list_kind (list t) = vpattern_replace (aparse _ cur') in
    f_false _ cur _;
    let vcur1 = intro_singleton _ cur in
    List.Tot.append_assoc vbin.contents vcur1.contents vcur'.contents;
    let vbin' = list_append _ bin cur in
    rewrite (state _ _) (state false vbin'.contents);
    list_iter_with_interrupt_close_false p state f_false _ bin cur' _ _
  end

#pop-options

#push-options "--z3rlimit 64"
#restart-solver

let list_iter_with_interrupt_close
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (state: bool -> list t -> vprop)
  (f_false: (
    (#opened: _) ->
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (l: Ghost.erased (list t)) ->
    STGhostT unit opened
      (aparse p a va `star` state false l)
      (fun res -> aparse p a va `star` state false (List.Tot.snoc (Ghost.reveal l, va.contents)))
  ))  
  (v0: v parse_list_kind (list t))
  (bin: byte_array)
  (bcur: R.ref byte_array)
  (bsz: R.ref SZ.size_t)
  (bcont: R.ref bool)
  (bloop_cont: R.ref bool)
: STGhost (Ghost.erased bool) opened
    (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont false)
    (fun cont ->
      R.pts_to bcont full_perm cont `star`
      state cont v0.contents `star`
      aparse (parse_list p) bin v0 `star`
      exists_ (R.pts_to bcur full_perm) `star`
      exists_ (R.pts_to bsz full_perm) `star`
      exists_ (R.pts_to bloop_cont full_perm)
    )
    (k.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= rewrite
    (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont false)
    (list_iter_with_interrupt_inv0 p state v0 bin bcur bsz bcont bloop_cont false);
  let _ = gen_elim () in
  let cont : bool = vpattern_replace (fun cont -> R.pts_to bcont full_perm cont `star` state cont _) in
  let vbin : v _ _ = vpattern_replace (fun (vbin: v _ _) -> aparse (parse_list p) bin vbin `star` state _ vbin.contents) in
  let cur = vpattern_replace (fun cur -> R.pts_to bcur full_perm cur `star` aparse _ cur _) in
  if cont
  then begin
    let _ = ghost_is_cons p cur in
    List.Tot.append_l_nil vbin.contents;
    let _ = list_append _ bin cur in
    rewrite (aparse _ bin _) (aparse (parse_list p) bin v0);
    rewrite (state _ _) (state cont v0.contents);
    noop ();
    cont
  end else begin
    rewrite (state _ _) (state false vbin.contents);
    list_iter_with_interrupt_close_false p state f_false v0 bin cur _ _;
    rewrite (state _ _) (state cont v0.contents);
    noop ();
    cont
  end

#pop-options

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
let list_iter_with_interrupt_test
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (state: bool -> list t -> vprop)
  (v0: v parse_list_kind (list t))
  (bin: byte_array)
  (bcur: R.ref byte_array)
  (bsz: R.ref SZ.size_t)
  (bcont: R.ref bool)
  (bloop_cont: R.ref bool)
  ()
: STT bool
    (exists_ (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont))
    (fun loop_cont -> list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont loop_cont)
=
  let _ = gen_elim () in
  let gloop_cont = vpattern_replace_erased (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont) in
  rewrite
    (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont gloop_cont)
    (list_iter_with_interrupt_inv0 p state v0 bin bcur bsz bcont bloop_cont gloop_cont);
  let _ = gen_elim () in
  let loop_cont = read_replace bloop_cont in
  rewrite
    (list_iter_with_interrupt_inv0 p state v0 bin bcur bsz bcont bloop_cont loop_cont)
    (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont loop_cont);
  return loop_cont

#pop-options

let int_sub_intro (a b c: nat) : Lemma
  (requires (a + b == c))
  (ensures (
    c >= a /\
    b == c - a
  ))
= ()

#push-options "--z3rlimit 128 --split_queries --z3cliopt smt.arith.nl=false"
#restart-solver

inline_for_extraction
let list_iter_with_interrupt_body
  (#k: Ghost.erased parser_kind)
  (#t: Type)
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
  (v0: v parse_list_kind (list t))
  (bin: byte_array)
  (bcur: R.ref byte_array)
  (bsz: R.ref SZ.size_t)
  (bcont: R.ref bool)
  (bloop_cont: R.ref bool)
  (_: squash (
    k.parser_kind_subkind == Some ParserStrong
  ))
: STT unit
    (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont true)
    (fun _ -> exists_ (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont))
=
  rewrite
    (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont true)
    (list_iter_with_interrupt_inv0 p state v0 bin bcur bsz bcont bloop_cont true);
  let _ = gen_elim () in
  let vbin : v parse_list_kind (list t) = vpattern_replace (aparse _ bin) in
  let sz = R.read bsz in
  let cur = R.read bcur in
  vpattern_rewrite (fun cur -> R.pts_to bcur full_perm cur `star` aparse _ cur _) cur;
  let vcur = vpattern_replace (aparse _ cur) in
  assert (SZ.size_v sz == AP.length (array_of' vcur));
  let _ = ghost_is_cons p cur in
  let gcur' = ghost_elim_cons p cur in
  let _ = gen_elim () in
  let cur_sz = get_parsed_size j cur in
  let cur' = hop_aparse_aparse_with_size _ _ cur cur_sz gcur' in
  let vcur1 = vpattern (aparse p cur) in
  let vcur' : v parse_list_kind (list t) = vpattern (aparse (parse_list p) cur') in
//  assert (AP.merge_into (array_of' vcur1) (array_of' vcur') (array_of' vcur));
  int_sub_intro (SZ.size_v cur_sz) (AP.length (array_of' vcur')) (SZ.size_v sz);
  vpattern_rewrite (fun st -> state st _) true;
  let cont' = f_true _ cur _ in
  let vcur = intro_singleton _ cur in
  List.Tot.append_assoc vbin.contents vcur.contents vcur'.contents;
  let vbin' = list_append _ bin cur in
  rewrite
    (state _ _)
    (state cont' vbin'.contents);
  R.write bcur cur';
  let sz' = sz `SZ.size_sub` cur_sz in
  R.write bsz sz';
  R.write bcont cont';
  let loop_cont' = SZ.size_lt SZ.zero_size sz' && cont' in
  R.write bloop_cont loop_cont';
  rewrite
    (list_iter_with_interrupt_inv0 p state v0 bin bcur bsz bcont bloop_cont loop_cont')
    (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont loop_cont');
  noop ()

#pop-options

inline_for_extraction
let list_iter_with_interrupt
  (#k: Ghost.erased parser_kind)
  (#t: Type)
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
  (len: SZ.size_t)
: ST bool
    (aparse (parse_list p) bin v0 `star` state true [])
    (fun res -> aparse (parse_list p) bin v0 `star` state res v0.contents)
    (SZ.size_v len == AP.length (array_of v0) /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
= let _ = elim_aparse (parse_list p) bin in
  let cur = AP.split bin SZ.zero_size in
  let _ = gen_elim () in
  let vbin = intro_nil p bin in
  let vcur = intro_aparse (parse_list p) cur in
  let loop_cont = SZ.zero_size `SZ.size_lt` len in
  with_local cur (fun bcur ->
  with_local len (fun bsz ->
  with_local loop_cont (fun bloop_cont ->
  with_local true (fun bcont ->
    rewrite
      (state _ _)
      (state true vbin.contents);
    rewrite
      (list_iter_with_interrupt_inv0 p state v0 bin bcur bsz bcont bloop_cont loop_cont)
      (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont loop_cont);
    Steel.ST.Loops.while_loop
      (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont)
      (list_iter_with_interrupt_test p state v0 bin bcur bsz bcont bloop_cont)
      (list_iter_with_interrupt_body j state f_true v0 bin bcur bsz bcont bloop_cont);
    let _ = list_iter_with_interrupt_close p state f_false v0 bin bcur bsz bcont bloop_cont in
    let res = R.read bcont in
    rewrite
      (state _ _)
      (state res v0.contents);
    intro_exists _ (R.pts_to bcont full_perm);
    return res
  ))))
