module LowParse.SteelST.List.Iter.WithInterrupt

module R = Steel.ST.Reference
module LI = LowParse.SteelST.List.Iterator

open Steel.ST.GenElim

let list_iter_with_interrupt_prop
  (#t: Type)
  (vcur: v parse_list_kind (list t))
  (sz: SZ.t)
  (cont: bool)
  (loop_cont: bool)
: Tot prop
= SZ.v sz == AP.length (array_of' vcur) /\
  loop_cont == (SZ.v sz > 0 && cont)

[@@__reduce__]
let list_iter_with_interrupt_inv0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (state: bool -> list t -> vprop)
  (v0: v parse_list_kind (list t))
  (bin: byte_array)
  (bcur: R.ref byte_array)
  (bsz: R.ref SZ.t)
  (bcont: R.ref bool)
  (bloop_cont: R.ref bool)
  (loop_cont: bool)
: Tot vprop
= exists_ (fun (lbin: list t) -> exists_ (fun cur -> exists_ (fun (vcur: v parse_list_kind (list t)) -> exists_ (fun sz -> exists_ (fun cont ->
    R.pts_to bcur full_perm cur `star`
    aparse (parse_list p) cur vcur `star`
    R.pts_to bsz full_perm sz `star`
    R.pts_to bcont full_perm cont `star`
    state cont lbin `star`
    R.pts_to bloop_cont full_perm loop_cont `star`
    LI.list_iterator_strong p v0 bin lbin vcur `star`
    pure (
      list_iter_with_interrupt_prop vcur sz cont loop_cont
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
  (bsz: R.ref SZ.t)
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
  (lbin: list t)
  (vcur: v parse_list_kind (list t))
: STGhostT unit opened
    (LI.list_iterator_strong p v0 bin lbin vcur `star`
      aparse (parse_list p) cur vcur `star` state false lbin)
    (fun _ -> aparse (parse_list p) bin v0 `star` state false v0.contents)
    (decreases vcur.contents)
= LI.list_iterator_strong_facts _ _ _ _ _;
  if Nil? vcur.contents
  then begin
    List.Tot.append_l_nil lbin;
    LI.list_iterator_strong_end _ _ _ _;
    rewrite (state _ _) (state false v0.contents)
  end else begin
    let cur' = ghost_elim_cons _ cur in
    let _ = gen_elim () in
    let vcur' : v parse_list_kind (list t) = vpattern_replace (aparse _ cur') in
    f_false _ cur _;
    LI.list_iterator_strong_next p _ _ _ _;
    vpattern_rewrite (state _) _;
    list_iter_with_interrupt_close_false p state f_false _ bin cur' _ _
  end

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
  (bsz: R.ref SZ.t)
  (bcont: R.ref bool)
  (bloop_cont: R.ref bool)
: STGhostT (Ghost.erased bool) opened
    (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont false)
    (fun cont ->
      R.pts_to bcont full_perm cont `star`
      state cont v0.contents `star`
      aparse (parse_list p) bin v0 `star`
      exists_ (R.pts_to bcur full_perm) `star`
      exists_ (R.pts_to bsz full_perm) `star`
      exists_ (R.pts_to bloop_cont full_perm)
    )
= rewrite
    (list_iter_with_interrupt_inv p state v0 bin bcur bsz bcont bloop_cont false)
    (list_iter_with_interrupt_inv0 p state v0 bin bcur bsz bcont bloop_cont false);
  let _ = gen_elim () in
  let cont : bool = vpattern_replace (fun cont -> R.pts_to bcont full_perm cont `star` state cont _) in
  let lbin = vpattern_replace (fun l -> LI.list_iterator_strong p  _ _ l _) in
  let cur = vpattern_replace (fun cur -> R.pts_to bcur full_perm cur `star` aparse _ cur _) in
  LI.list_iterator_strong_facts _ _ _ _ _;
  if cont
  then begin
    let _ = ghost_is_cons p cur in
    List.Tot.append_l_nil lbin;
    LI.list_iterator_strong_end p _ _ _;
    rewrite (state _ _) (state cont v0.contents);
    noop ();
    cont
  end else begin
    rewrite (state _ _) (state false lbin);
    list_iter_with_interrupt_close_false p state f_false v0 bin cur _ _;
    rewrite (state _ _) (state cont v0.contents);
    noop ();
    cont
  end

#restart-solver

inline_for_extraction
let list_iter_with_interrupt_test
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // FIXME: if the universe is left out, then F* master will determine universe 0, but F* #2349 cannot, since gen_elim now allows universes 0 and 1. So let's stay at universe 0 for now.
  (p: parser k t)
  (state: bool -> list t -> vprop)
  (v0: v parse_list_kind (list t))
  (bin: byte_array)
  (bcur: R.ref byte_array)
  (bsz: R.ref SZ.t)
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

// #push-options "--z3rlimit 64 --split_queries always --z3cliopt smt.arith.nl=false"
#push-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false"
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
  (bsz: R.ref SZ.t)
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
  let sz = R.read bsz in
  let cur = R.read bcur in
  vpattern_rewrite (fun cur -> R.pts_to bcur full_perm cur `star` aparse _ cur _) cur;
  let vcur = vpattern_replace (aparse _ cur) in
  assert (SZ.v sz == AP.length (array_of' vcur));
  let _ = ghost_is_cons p cur in
  let gcur' = ghost_elim_cons p cur in
  let _ = gen_elim () in
  let cur_sz = get_parsed_size j cur in
  let cur' = hop_aparse_aparse_with_size _ _ cur cur_sz gcur' in
  let vcur1 = vpattern (aparse p cur) in
  let vcur' : v parse_list_kind (list t) = vpattern (aparse (parse_list p) cur') in
  int_sub_intro (SZ.v cur_sz) (AP.length (array_of' vcur')) (SZ.v sz);
  vpattern_rewrite (fun st -> state st _) true;
  let cont' = f_true _ cur _ in
  LI.list_iterator_strong_next p _ _ cur _;
  rewrite
    (state _ _)
    (state cont' _);
  R.write bcur cur';
  let sz' = sz `SZ.sub` cur_sz in
  R.write bsz sz';
  R.write bcont cont';
  let loop_cont' = SZ.lt 0sz sz' && cont' in
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
  (len: SZ.t)
: ST bool
    (aparse (parse_list p) bin v0 `star` state true [])
    (fun res -> aparse (parse_list p) bin v0 `star` state res v0.contents)
    (SZ.v len == AP.length (array_of v0) /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
= let vcur = LI.list_iterator_strong_begin p bin in
  let loop_cont = 0sz `SZ.lt` len in
  with_local bin (fun bcur ->
  with_local len (fun bsz ->
  with_local loop_cont (fun bloop_cont ->
  with_local true (fun bcont ->
    noop ();
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
