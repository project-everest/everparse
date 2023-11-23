module LowParse.SteelST.List.Map

open LowParse.SteelST.List.Iter.ConsumesWithArray
open LowParse.SteelST.List.Iter.ReadOnly
open Steel.ST.GenElim

module R = Steel.ST.Reference
module P = Steel.FractionalPermission

let list_map_inplace_le_opt_prop
  (#t: Type)
  (#t': Type)
  (phi: Ghost.erased (t -> t'))
  (al: AP.array byte)
  (l: list t)
  (wl: v parse_list_kind _)
  (len: _)
  (wout: _)
: Tot prop
=
    SZ.v len == AP.length (array_of' wl) /\
    AP.merge_into (array_of' wl) (AP.array_of wout) al /\
    wl.contents == List.Tot.map phi l

[@@__reduce__]
let list_map_inplace_le_opt_state0
  (#t: Type)
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t')
  (phi: Ghost.erased (t -> t'))
  (out0: byte_array)
  (pout: R.ref byte_array)
  (plen: R.ref SZ.t)
  (al: AP.array byte)
  (_: unit)
  (l: list t)
: Tot vprop
= exists_ (fun (wl: v _ _) -> exists_ (fun len -> exists_ (fun out -> exists_ (fun wout ->
    aparse (parse_list p') out0 wl `star`
    R.pts_to plen P.full_perm len `star`
    R.pts_to pout P.full_perm out `star`
    AP.arrayptr out wout `star` pure (
    list_map_inplace_le_opt_prop phi al l wl len wout
  )))))

let list_map_inplace_le_opt_state
  (#t: Type)
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t')
  (phi: Ghost.erased (t -> t'))
  (out0: byte_array)
  (pout: R.ref byte_array)
  (plen: R.ref SZ.t)
  (al: AP.array byte)
  (q: unit)
  (l: list t)
: Tot vprop
= list_map_inplace_le_opt_state0 p' phi out0 pout plen al q l

#push-options "--z3rlimit 64"

#restart-solver
inline_for_extraction
let list_map_inplace_le_opt
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p { k.parser_kind_subkind == Some ParserStrong })
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t' { k'.parser_kind_subkind == Some ParserStrong })
  (phi: Ghost.erased (t -> t'))
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (vout: AP.v byte { AP.adjacent (AP.array_of vout) (array_of' va) }) -> // TODO: add write permissions
    (out: byte_array) ->
    STT SZ.t
      (aparse p a va `star` AP.arrayptr out vout)
      (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
        aparse p' out vout' `star` AP.arrayptr res' vres' `star` pure (
        SZ.v res == AP.length (array_of vout') /\
        SZ.v res > 0 /\
        AP.merge_into (array_of' vout') (AP.array_of vres') (AP.merge (AP.array_of vout) (array_of' va)) /\
        vout'.contents == Ghost.reveal phi va.contents
      )))))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.t { SZ.v len == length_opt va.array })
  (#vout: _)
  (out: byte_array { adjacent_opt (AP.array_of vout) va.array })  // TODO: add write permissions
: STT SZ.t
    (aparse_list p a va `star` AP.arrayptr out vout)
    (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
      aparse (parse_list p') out vout' `star` AP.arrayptr res' vres' `star` pure (
      SZ.v res == AP.length (array_of' vout') /\
      AP.merge_into (array_of' vout') (AP.array_of vres') (merge_opt (AP.array_of vout) va.array) /\
      vout'.contents == List.Tot.map phi va.contents
    )))))
= let al0 = AP.array_of vout in
  let afull = merge_opt al0 va.array in
  let out1 = AP.split out 0sz in
  let _ = gen_elim () in
  let _ = intro_nil p' out in
  with_local 0sz (fun plen ->
  with_local out1 (fun pout ->
  noop ();
  rewrite
    (list_map_inplace_le_opt_state0 p' phi out pout plen al0 () [])
    (list_map_inplace_le_opt_state p' phi out pout plen al0 () []);
  let psi (_: unit) (_: t) : Tot unit = () in
  list_iter_consumes_with_array
    j
    psi
    (list_map_inplace_le_opt_state p' phi out pout plen)
    (fun va1 a1 al1 accu l ->
      rewrite
        (list_map_inplace_le_opt_state p' phi out pout plen _ _ _)
        (list_map_inplace_le_opt_state0 p' phi out pout plen al1 () l);
      let _ = gen_elim () in
      let out1 = read_replace pout in
      vpattern_rewrite (fun out1 -> AP.arrayptr out1 _) out1;
      let len1 = f va1 a1 _ out1 in
      let _ = gen_elim () in
      let len = R.read plen in
      let len' = SZ.add len len1 in
      R.write plen len';
      let _ = elim_aparse p' out1 in
      let out2 = AP.split' out1 len1 _ in
      let _ = intro_aparse p' out1 in
      R.write pout out2;
      let vout1' = intro_singleton p' out1 in
      let _ = list_append p' out out1 in
      let al1' = AP.merge al1 (array_of' va1) in
      let l' = Ghost.hide (l `List.Tot.append` [va1.contents]) in
      List.Tot.map_append phi l [va1.contents];
      list_iter_consumes_with_array_body_post_intro k psi va1 al1 accu l al1' l' ();
      noop ();
      rewrite
        (list_map_inplace_le_opt_state0 p' phi out pout plen al1' () l')
        (list_map_inplace_le_opt_state p' phi out pout plen al1' () l');
      return ()
    )
    a len al0 ()
    ;
  let _ = gen_elim () in
  rewrite
    (list_map_inplace_le_opt_state p' phi out pout plen _ _ _)
    (list_map_inplace_le_opt_state0 p' phi out pout plen afull () va.contents);
  let _ = gen_elim () in
  let res = R.read plen in
  noop ();
  return res
  ))

#pop-options

#push-options "--z3rlimit 16"

inline_for_extraction
let list_map_inplace_le
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p { k.parser_kind_subkind == Some ParserStrong })
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t' { k'.parser_kind_subkind == Some ParserStrong })
  (phi: Ghost.erased (t -> t'))
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) ->
    (a: byte_array) ->
    (vout: AP.v byte { AP.adjacent (AP.array_of vout) (array_of' va) }) -> // TODO: add write permissions
    (out: byte_array) ->
    STT SZ.t
      (aparse p a va `star` AP.arrayptr out vout)
      (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
        aparse p' out vout' `star` AP.arrayptr res' vres' `star` pure (
        SZ.v res == AP.length (array_of vout') /\
        SZ.v res > 0 /\
        AP.merge_into (array_of' vout') (AP.array_of vres') (AP.merge (AP.array_of vout) (array_of' va)) /\
        vout'.contents == Ghost.reveal phi va.contents
      )))))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.t { SZ.v len == AP.length (array_of' va) })
  (#vout: _)
  (out: byte_array { AP.adjacent (AP.array_of vout) (array_of' va) })  // TODO: add write permissions
: STT SZ.t
    (aparse (parse_list p) a va `star` AP.arrayptr out vout)
    (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
      aparse (parse_list p') out vout' `star` AP.arrayptr res' vres' `star` pure (
      SZ.v res == AP.length (array_of' vout') /\
      AP.merge_into (array_of' vout') (AP.array_of vres') (AP.merge (AP.array_of vout) (array_of' va)) /\
      vout'.contents == List.Tot.map phi va.contents
    )))))
= intro_aparse_list p out a;
  let _ = gen_elim () in
  let res = list_map_inplace_le_opt j p' phi f a len out in
  let _ = gen_elim () in
  return res

#pop-options

[@@__reduce__]
let list_map_inplace_eq_state0
  (#t: Type)
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t')
  (phi: Ghost.erased (t -> t'))
  (a0: byte_array)
  (al: AP.array byte)
  (_: unit)
  (l: list t)
: Tot vprop
= exists_ (fun (wl: v _ _) ->
    aparse (parse_list p') a0 wl `star` pure (
    array_of' wl == al /\
    wl.contents == List.Tot.map phi l
  ))

let list_map_inplace_eq_state
  (#t: Type)
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t')
  (phi: Ghost.erased (t -> t'))
  (a0: byte_array)
  (al: AP.array byte)
  (q: unit)
  (l: list t)
: Tot vprop
= list_map_inplace_eq_state0 p' phi a0 al q l

#push-options "--z3rlimit 16"

inline_for_extraction
let list_map_inplace_eq
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p { k.parser_kind_subkind == Some ParserStrong })
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t' { k'.parser_kind_subkind == Some ParserStrong })
  (phi: Ghost.erased (t -> t'))
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) -> // TODO: add write permissions
    (a: byte_array) ->
    STT (v k' t')
      (aparse p a va)
      (fun va' -> aparse p' a va' `star` pure (
        array_of' va' == array_of' va /\
        va'.contents == Ghost.reveal phi va.contents
      ))
  ))
  (#va: v _ _)
  (a: byte_array)
  (len: SZ.t)
: ST (v _ _)
    (aparse (parse_list p) a va)
    (fun va' -> aparse (parse_list p') a va')
    (SZ.v len == AP.length (array_of' va))  // TODO: add write permissions
    (fun va' ->
      array_of' va' == array_of' va /\
      va'.contents == List.Tot.map phi va.contents
    )
= list_split_nil_l p a;
  let _ = gen_elim () in
  let vr0 = vpattern_replace (fun vr -> aparse_list p a vr) in
  let _ = elim_nil p a in
  let va0 = intro_nil p' a in
  let al = array_of' va0 in
  let psi (_: unit) (_: t) : Tot unit = () in
  noop ();
  rewrite
    (list_map_inplace_eq_state0 p' phi a al () [])
    (list_map_inplace_eq_state p' phi a al () []);
  list_iter_consumes_with_array
    j
    psi
    (list_map_inplace_eq_state p' phi a)
    (fun va1 a1 al1 accu l ->
      rewrite
        (list_map_inplace_eq_state p' phi a _ _ _)
        (list_map_inplace_eq_state0 p' phi a al1 () l);
      let _ = gen_elim () in
      let _ = f va1 a1 in
      let _ = gen_elim () in
      let _ = intro_singleton p' a1 in 
      let va' = list_append p' a a1 in
      let al1' = array_of' va' in
      let l' = Ghost.hide (l `List.Tot.append` [va1.contents]) in
      List.Tot.map_append phi l [va1.contents];
      list_iter_consumes_with_array_body_post_intro k psi va1 al1 accu l al1' l' ();
      noop ();
      rewrite
        (list_map_inplace_eq_state0 p' phi a al1' () l')
        (list_map_inplace_eq_state p' phi a al1' () l');
      return ()
    )
    a len al ()
    ;
  let _ = gen_elim () in
  rewrite
    (list_map_inplace_eq_state p' phi a _ _ _)
    (list_map_inplace_eq_state0 p' phi a (array_of' va) () va.contents);
  let _ = gen_elim () in
  let res = vpattern_replace (fun va' -> aparse (parse_list p') a va') in
  return res

#pop-options

inline_for_extraction
let list_map_inplace_eq_opt
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p { k.parser_kind_subkind == Some ParserStrong })
  (#k': parser_kind)
  (#t': Type)
  (p': parser k' t' { k'.parser_kind_subkind == Some ParserStrong })
  (phi: Ghost.erased (t -> t'))
  (f: (
    (va: v k t { AP.length (array_of' va) > 0 }) -> // TODO: add write permissions
    (a: byte_array) ->
    STT (v k' t')
      (aparse p a va)
      (fun va' -> aparse p' a va' `star` pure (
        array_of' va' == array_of' va /\
        va'.contents == Ghost.reveal phi va.contents
      ))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.t)
: ST _
    (aparse_list p a va)
    (fun va' -> aparse_list p' a va')
    (SZ.v len == length_opt va.array)  // TODO: add write permissions
    (fun va' ->
      va'.array == va.array /\
      va'.contents == List.Tot.map phi va.contents
    )
= let _ = ghost_is_cons_opt p a in
  if len = 0sz
  then begin
    elim_aparse_list_nil p a _;
    intro_aparse_list_nil p' a
  end else begin
    let _ = elim_aparse_list_cons p a _ in
    let _ = list_map_inplace_eq j p' phi f a len in
    intro_aparse_list_cons p' a _
  end
