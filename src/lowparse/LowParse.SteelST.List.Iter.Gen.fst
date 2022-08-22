module LowParse.SteelST.List.Iter.Gen

#set-options "--ide_id_info_off"

open Steel.ST.GenElim

let list_iter_gen_prop
  (#t: Type)
  (#t': Type)
  (phi: t' -> t -> t')
  (enable_arrays: bool)
  (init: t')
  (l0: list t)
  (afull: option (AP.array byte))
  (va: _)
  (len: _)
  (accu: _)
  (al: _)
  (l: _)
  (cont: _)
: Tot prop
= 
    SZ.size_v len == length_opt va.array /\
    accu == List.Tot.fold_left phi init l /\
    l0 == l `List.Tot.append` va.contents /\
    cont == Cons? va.contents /\
    (enable_arrays ==> (
      Some? al /\ Some? afull /\ merge_opt_into (Some?.v al) va.array (Some?.v afull)
    ))

module R = Steel.ST.Reference

[@@__reduce__]
let list_iter_gen_inv0
  (#k: parser_kind)
  (#t: Type)
  (#t': Type)
  (p: parser k t)
  (phi: t' -> t -> t')
  (enable_arrays: bool)
  (state: option (AP.array byte) -> t' -> list t -> vprop)
  (init: t')
  (l0: list t)
  (afull: option (AP.array byte))
  (pa: R.ref byte_array)
  (plen: R.ref SZ.size_t)
  (paccu: R.ref t')
  (pcont: R.ref bool)
  (cont: bool)
: Tot vprop
= exists_ (fun a -> exists_ (fun va -> exists_ (fun len -> exists_ (fun accu -> exists_ (fun al -> exists_ (fun l ->
    R.pts_to pa P.full_perm a `star`
    aparse_list p a va `star`
    R.pts_to plen P.full_perm len `star`
    R.pts_to paccu P.full_perm accu `star`
    R.pts_to pcont P.full_perm cont `star`
    state al accu l `star` pure (
    list_iter_gen_prop phi enable_arrays init l0 afull va len accu al l cont
  )))))))

let list_iter_gen_inv
  (#k: parser_kind)
  (#t: Type)
  (#t': Type)
  (p: parser k t)
  (phi: t' -> t -> t')
  (enable_arrays: bool)
  (state: option (AP.array byte) -> t' -> list t -> vprop)
  (init: t')
  (l0: list t)
  (afull: option (AP.array byte))
  (pa: R.ref byte_array)
  (plen: R.ref SZ.size_t)
  (paccu: R.ref t')
  (pcont: R.ref bool)
  (cont: bool)
: Tot vprop
= list_iter_gen_inv0 p phi enable_arrays state init l0 afull pa plen paccu pcont cont

let list_iter_gen_inv_intro #opened #k #t #t' p phi enable_arrays state init l0 afull pa plen paccu pcont cont
: STGhostT unit opened
    (list_iter_gen_inv0 #k #t #t' p phi enable_arrays state init l0 afull pa plen paccu pcont cont)
    (fun _ -> list_iter_gen_inv #k #t #t' p phi enable_arrays state init l0 afull pa plen paccu pcont cont)
= noop () // by F* unification rather than the framing tactic

let list_iter_gen_inv_elim #opened #k #t #t' p phi enable_arrays state init l0 afull pa plen paccu pcont cont
: STGhostT unit opened
    (list_iter_gen_inv #k #t #t' p phi enable_arrays state init l0 afull pa plen paccu pcont cont)
    (fun _ -> list_iter_gen_inv0 #k #t #t' p phi enable_arrays state init l0 afull pa plen paccu pcont cont)
= noop () // by F* unification rather than the framing tactic

#push-options "--z3rlimit 64"

#restart-solver
inline_for_extraction
let list_iter_gen_body
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p {k.parser_kind_subkind == Some ParserStrong})
  (#t': Type)
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
  (va: _)
  (init: t')
  (afull: Ghost.erased (option (AP.array byte)))
  (pa: R.ref byte_array)
  (plen: R.ref SZ.size_t)
  (paccu: R.ref t')
  (pcont: R.ref bool)
  ()
: STT unit
    (list_iter_gen_inv p phi enable_arrays state init va.contents afull pa plen paccu pcont true)
    (fun _ -> exists_ (list_iter_gen_inv p phi enable_arrays state init va.contents afull pa plen paccu pcont))
=
      list_iter_gen_inv_elim p phi enable_arrays state init va.contents afull pa plen paccu pcont _;
      let _ = gen_elim () in
      let a = read_replace pa in
      vpattern_rewrite (fun a_ -> aparse_list p a_ _) a;
      let va1 = vpattern (fun va1 -> aparse_list p a va1) in
      let va1' = elim_aparse_list_cons p a _ in
      let a' = ghost_elim_cons p a in
      let _ = gen_elim () in
      let alen = get_parsed_size j a in
      let a' = elim_cons_opt_with_length p a alen a' in
      let _ = gen_elim () in
      let accu = R.read paccu in
      let l = vpattern_replace_erased (fun l -> state _ _ l) in
      let al = vpattern_replace_erased (fun al -> state al _ _) in
      vpattern_rewrite (fun accu -> state _ accu _) accu;
      let va_ = vpattern (fun va -> aparse p a va) in
      let vq = vpattern (fun vq -> aparse_list p a' vq) in
      let _ = ghost_is_cons_opt p a' in
      let accu' = f _ a al accu l in
      let _ = gen_elim () in
      let len = R.read plen in
      let len' = len `SZ.size_sub` alen in
      let al' = vpattern_erased (fun al' -> state al' _ _) in
      list_append_cons_r l va_.contents vq.contents;
      list_fold_left_snoc phi init l va_.contents;
      Classical.impl_intro_gen
        #(Ghost.reveal enable_arrays)
        #(fun _ -> Some? al' /\ Some? afull /\ merge_opt_into (Some?.v al') vq.array (Some?.v afull))
        (fun _ ->
          merge_opt_into_r (Some?.v al) va1.array (Some?.v afull) (array_of' va1') (array_of' va_) vq.array
        );
      R.write plen len';
      R.write pa a';
      R.write paccu accu';
      R.write pcont (len' <> SZ.zero_size);
      list_iter_gen_inv_intro p phi enable_arrays state init va.contents afull pa plen paccu pcont _;
      return ()

#pop-options

  let compute_afull
    (enable_arrays: Ghost.erased bool)
    (va: _)
    (al: Ghost.erased (option (AP.array byte)))
  : Pure (Ghost.erased (option (AP.array byte)))
      (Ghost.reveal enable_arrays ==> (Some? al /\ adjacent_opt (Some?.v al) va.array))
      (fun afull ->
        Ghost.reveal enable_arrays ==> (
          Some? al /\ Some? afull /\ merge_opt_into (Some?.v al) va.array (Some?.v afull)
      ))
  =
    if Ghost.reveal enable_arrays
    then Ghost.hide (Some (merge_opt (Some?.v al) va.array))
    else Ghost.hide None

module L = Steel.ST.Loops

#push-options "--z3rlimit 32 --print_universes"

#restart-solver
inline_for_extraction
let list_iter_gen
  #k #t #p j #t' phi enable_arrays state f #va a len al init
=
  let afull = compute_afull enable_arrays va al in
  with_local a (fun pa ->
  with_local len (fun plen ->
  with_local init (fun paccu ->
  with_local (len <> SZ.zero_size) (fun pcont ->
  let _ = ghost_is_cons_opt p a in
  list_iter_gen_inv_intro p phi enable_arrays state init va.contents afull pa plen paccu pcont _;
  L.while_loop
    (list_iter_gen_inv p phi enable_arrays state init va.contents afull pa plen paccu pcont)
    (fun _ ->
      let _ = gen_elim () in
      list_iter_gen_inv_elim p phi enable_arrays state init va.contents afull pa plen paccu pcont _;
      let _ = gen_elim () in
      let res = read_replace pcont in
      list_iter_gen_inv_intro p phi enable_arrays state init va.contents afull pa plen paccu pcont res;
      return res
    )
    (list_iter_gen_body j phi enable_arrays state f va init afull pa plen paccu pcont);
  list_iter_gen_inv_elim p phi enable_arrays state init va.contents afull pa plen paccu pcont _;
  let _ = gen_elim () in
  let l' = vpattern_erased (fun l' -> state _ _ l') in
  List.Tot.append_l_nil l';
  let a' = read_replace pa in
  vpattern_rewrite (fun a' -> aparse_list p a' _) a';
  elim_aparse_list_nil p a' _;
  let res = R.read paccu in
  let ar' = vpattern_erased (fun ar' -> state ar' _ _) in
  vpattern_rewrite (fun res -> state _ res _) res;
  vpattern_rewrite (fun l' -> state _ _ l') va.contents;
  return res
  ))))

#pop-options
