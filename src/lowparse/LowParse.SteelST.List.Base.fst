module LowParse.SteelST.List.Base

open Steel.ST.GenElim

module L = Steel.ST.Loops

#set-options "--ide_id_info_off"

let intro_nil
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (AP.arrayptr a va)
    (fun va' -> aparse (parse_list p) a va')
    (AP.length (AP.array_of va) == 0)
    (fun va' ->
      array_of va' == AP.array_of va /\
      va'.contents == []
    )
= parse_list_eq p (AP.contents_of va);
  intro_aparse (parse_list p) a

let intro_cons
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1: _)
  (#va2: _)
  (a1 a2: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse p a1 va1 `star` aparse (parse_list p) a2 va2)
    (fun va -> aparse (parse_list p) a1 va)
    (k.parser_kind_subkind == Some ParserStrong /\
      AP.length (array_of va1) > 0 /\
      AP.adjacent (array_of va1) (array_of va2))
    (fun va ->
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents :: va2.contents
    )
= let va1' = elim_aparse p a1 in
  let va2' = elim_aparse (parse_list p) a2 in
  let va' = AP.join a1 a2 in
  let _ = gen_elim () in
  parse_list_eq p (AP.contents_of va');
  parse_strong_prefix p (AP.contents_of va1') (AP.contents_of va');
  assert (AP.contents_of' va2' `Seq.equal` Seq.slice (AP.contents_of' va') (AP.length (AP.array_of va1')) (AP.length (AP.array_of va')));
  intro_aparse (parse_list p) a1

let elim_nil
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (AP.v byte) opened
    (aparse (parse_list p) a va)
    (fun va' -> AP.arrayptr a va')
    (Nil? va.contents)
    (fun va' ->
      array_of va == AP.array_of va' /\
      AP.length (AP.array_of va') == 0
    )
= let res = elim_aparse (parse_list p) a in
  parse_list_eq p (AP.contents_of res);
  noop ();
  res

let ghost_elim_cons
  #opened #k #t p #va a
= let va' = elim_aparse (parse_list p) a in
  parse_list_eq p (AP.contents_of va');
  let a2 = ghost_peek_strong p a in
  let _ = gen_elim () in
  let _ = intro_aparse (parse_list p) a2 in
  a2

#push-options "--z3rlimit 16"

inline_for_extraction
let elim_cons
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#va: _)
  (a: byte_array)
: ST byte_array
    (aparse (parse_list p) a va)
    (fun a2 -> exists_ (fun va1 -> exists_ (fun va2 ->
      aparse p a va1 `star`
      aparse (parse_list p) a2 va2 `star` pure (
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents :: va2.contents /\
      AP.length (array_of va1) > 0
    ))))
    (Cons? va.contents /\ k.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= let gres = ghost_elim_cons p a in
  let _ = gen_elim () in
  let res = hop_aparse_aparse j (parse_list p) a gres in
  res

#pop-options

let ghost_is_cons
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (Ghost.erased bool) opened
    (aparse (parse_list p) a va)
    (fun _ -> aparse (parse_list p) a va)
    True
    (fun res ->
      (Ghost.reveal res == (AP.length (array_of va) > 0)) /\
      (Ghost.reveal res == Cons? va.contents)
    )
= let va' = elim_aparse (parse_list p) a in
  parse_list_eq p (AP.contents_of va');
  let res = Ghost.hide (AP.length (array_of va) > 0) in
  let _ = intro_aparse (parse_list p) a in
  rewrite (aparse (parse_list p) a _) (aparse (parse_list p) a va);
  res

let list_append_nil_l
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1 #va2: _)
  (a1 a2: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_list p) a1 va1 `star` aparse (parse_list p) a2 va2)
    (fun va -> aparse (parse_list p) a1 va)
    (AP.adjacent (array_of va1) (array_of va2) /\
      Nil? va1.contents)
    (fun va ->
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va2.contents
    )
= let _ = elim_nil p a1 in
  let va2' = elim_aparse (parse_list p) a2 in
  let va1' = AP.join a1 a2 in
  assert (AP.contents_of va2' `Seq.equal` AP.contents_of va1');
  intro_aparse (parse_list p) a1

#push-options "--z3rlimit 16 --query_stats"

let rec list_append
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1 #va2: _)
  (a1 a2: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_list p) a1 va1 `star` aparse (parse_list p) a2 va2)
    (fun va -> aparse (parse_list p) a1 va)
    (AP.adjacent (array_of va1) (array_of va2) /\
      k.parser_kind_subkind == Some ParserStrong)
    (fun va ->
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents `List.Tot.append` va2.contents
    )
    (decreases va1.contents)
= let gb = ghost_is_cons p a1 in
  let b = Ghost.reveal gb in
  if not gb
  then
    list_append_nil_l p a1 a2
  else begin
    let a15 = ghost_elim_cons p a1 in
    let _ = gen_elim () in
    let _ = list_append p a15 a2 in
    intro_cons p a1 a15
  end

#pop-options

let rec valid_list_total_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (b: bytes)
: Lemma
  (requires (
    k.parser_kind_low > 0 /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata == Some ParserKindMetadataTotal
  ))
  (ensures (
      Seq.length b % k.parser_kind_low == 0 <==> Some? (parse (parse_list p) b)
  ))
  (decreases (Seq.length b))
= parse_list_eq p b;
  if Seq.length b = 0
  then ()
  else begin
    parser_kind_prop_equiv k p;
    if Seq.length b < k.parser_kind_low
    then FStar.Math.Lemmas.modulo_lemma (Seq.length b) k.parser_kind_low
    else begin
      FStar.Math.Lemmas.sub_div_mod_1 (Seq.length b) k.parser_kind_low;
      valid_list_total_constant_size p (Seq.slice b k.parser_kind_low (Seq.length b))
    end
  end

inline_for_extraction
let validate_list_total_constant_size
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (sz: SZ.size_t)
: Pure (validator (parse_list p))
    (requires (
      k.parser_kind_low > 0 /\
      k.parser_kind_low == SZ.size_v sz /\
      k.parser_kind_high == Some k.parser_kind_low /\
      k.parser_kind_metadata == Some ParserKindMetadataTotal
    ))
    (ensures (fun _ -> True))
= fun #b a len err ->
  valid_list_total_constant_size p (AP.contents_of b);
  parser_kind_prop_equiv parse_list_kind (parse_list p);
  if len `SZ.size_mod` sz = SZ.zero_size
  then begin
    noop ();
    return len
  end else begin
    R.write err validator_error_not_enough_data;
    return SZ.zero_size
  end

let validate_list_pred
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (va0: _)
  (len0: SZ.size_t)
  (va: _)
  (vl: _)
  (len: _)
  (verr: U32.t)
  (cont: _)
: Tot prop
= AP.contents_of va0 `Seq.equal` (AP.contents_of vl `Seq.append` AP.contents_of va) /\
  AP.merge_into (AP.array_of vl) (AP.array_of va) (AP.array_of va0) /\
  Some? (parse (parse_list p) (AP.contents_of va0)) == Some? (parse (parse_list p) (AP.contents_of va)) /\
  SZ.size_v len0 == AP.length (AP.array_of va0) /\
  SZ.size_v len == AP.length (AP.array_of vl) /\
  ((~ (verr == 0ul)) ==> None? (parse (parse_list p) (AP.contents_of va0))) /\
  (cont == true ==> (verr == 0ul /\ ~ (len == len0))) /\
  ((cont == false /\ verr == 0ul) ==> len == len0)

[@@__reduce__]
let validate_list_inv0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a0: byte_array)
  (va0: _)
  (len0: SZ.size_t)
  (plen: R.ref SZ.size_t)
  (err: R.ref U32.t)
  (cont: bool)
: Tot vprop
= exists_ (fun len -> exists_ (fun vl -> exists_ (fun a -> exists_ (fun va -> exists_ (fun verr ->
    R.pts_to plen full_perm len `star`
    AP.arrayptr a0 vl `star`
    AP.arrayptr a va `star`
    R.pts_to err full_perm verr `star`
    pure (validate_list_pred p va0 len0 va vl len verr cont)
  )))))

let validate_list_inv
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a0: byte_array)
  (va0: _)
  (len0: SZ.size_t)
  (plen: R.ref SZ.size_t)
  (err: R.ref U32.t)
  (cont: bool)
: Tot vprop
= validate_list_inv0 p a0 va0 len0 plen err cont

inline_for_extraction
let validate_list_test
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va0: _)
  (a0: _)
  (len0: _)
  (err: _)
  (plen: _)
  ()
: STT bool
    (exists_ (validate_list_inv p a0 va0 len0 plen err))
    (validate_list_inv p a0 va0 len0 plen err)
=
      let _ = gen_elim () in
      let gcont = vpattern_erased (validate_list_inv p a0 va0 len0 plen err) in
      rewrite (validate_list_inv p a0 va0 len0 plen err _) (validate_list_inv0 p a0 va0 len0 plen err gcont);
      let _ = gen_elim () in
      let va = vpattern (fun va -> AP.arrayptr a0 _ `star` AP.arrayptr _ va) in
      parse_list_eq p (AP.contents_of va);
      let len = R.read plen in
      let verr = R.read err in
      let cont = (len <> len0 && verr = 0ul) in
      noop ();
      rewrite (validate_list_inv0 p a0 va0 len0 plen err cont) (validate_list_inv p a0 va0 len0 plen err cont);
      return cont

#push-options "--z3rlimit 32"

#restart-solver
inline_for_extraction
let validate_list_body
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
  (#va0: _)
  (a0: _)
  (len0: _)
  (err: _)
  (plen: _)
  ()
: STT unit
    (validate_list_inv p a0 va0 len0 plen err true)
    (fun _ -> exists_ (validate_list_inv p a0 va0 len0 plen err))
= rewrite (validate_list_inv p a0 va0 len0 plen err true) (validate_list_inv0 p a0 va0 len0 plen err true);
  let _ = gen_elim () in
  let len = R.read plen in
  let a = AP.split' a0 len _ in
  let va = vpattern (fun va -> AP.arrayptr a va) in
  parse_list_eq p (AP.contents_of va);
  let lenr = len0 `SZ.size_sub` len in
  let len1 = v a lenr err in
  let _ = gen_elim () in
  let verr = R.read err in
  if verr <> 0ul returns STT unit _ (fun _ -> exists_ (validate_list_inv p a0 va0 len0 plen err)) // necessary in general, but I am using if-then-else only in terminal position
  then begin
    noop ();
    rewrite (validate_list_inv0 p a0 va0 len0 plen err false) (validate_list_inv p a0 va0 len0 plen err false);
    return ()
  end else if len1 = SZ.zero_size 
  then begin
    R.write err validator_error_not_enough_data;
    noop (); // (Error) folding guard g2 of e2 in the lcomp; The SMT solver could not prove the query, try to spell your proof in more detail or increase fuel/ifuel
    rewrite (validate_list_inv0 p a0 va0 len0 plen err false) (validate_list_inv p a0 va0 len0 plen err false);
    return ()
  end else begin
    let len' = len `SZ.size_add` len1 in
    R.write plen len';
    let _ = AP.gsplit a len1 in
    let _ = gen_elim () in
    let _ = AP.join a0 a in
    rewrite (validate_list_inv0 p a0 va0 len0 plen err (len' <> len0)) (validate_list_inv p a0 va0 len0 plen err (len' <> len0));
    return ()
  end

#pop-options

inline_for_extraction
let with_local
  (#t: Type)
  (init: t)
  (#pre: vprop)
  (#ret_t: Type)
  (#post: ret_t -> vprop)
  (body: (r: R.ref t) ->
    STT ret_t
    (R.pts_to r full_perm init `star` pre)
    (fun v -> exists_ (R.pts_to r full_perm) `star` post v)
  )
: STF ret_t pre post True (fun _ -> True)
= R.with_local init body

inline_for_extraction // this one is fine
let with_ghost_local
  (#t: Type)
  (init: Ghost.erased t)
  (#pre: vprop)
  (#ret_t: Type)
  (#post: ret_t -> vprop)
  (body: (r: GR.ref t) ->
    STT ret_t
    (GR.pts_to r full_perm init `star` pre)
    (fun v -> exists_ (GR.pts_to r full_perm) `star` post v)
  )
: STF ret_t pre post True (fun _ -> True)
= GR.with_local init body

#push-options "--z3rlimit 16"

inline_for_extraction
let validate_list
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator p)
: Tot (validator (parse_list p))
= fun #va0 a0 len0 err ->
  parse_list_eq p (AP.contents_of va0);
  with_local SZ.zero_size (fun plen ->
  let _ = AP.gsplit a0 SZ.zero_size in
  let _ = gen_elim () in
  rewrite (validate_list_inv0 p a0 va0 len0 plen err (len0 <> SZ.zero_size)) (validate_list_inv p a0 va0 len0 plen err (len0 <> SZ.zero_size));
  L.while_loop
    (validate_list_inv p a0 va0 len0 plen err)
    (validate_list_test p a0 len0 err plen)
    (validate_list_body v a0 len0 err plen);
  rewrite (validate_list_inv p a0 va0 len0 plen err false) (validate_list_inv0 p a0 va0 len0 plen err false);
  let _ = gen_elim () in
  let va = vpattern (fun va -> AP.arrayptr a0 _ `star` AP.arrayptr _ va) in
  parse_list_eq p (AP.contents_of va);
  parser_kind_prop_equiv parse_list_kind (parse_list p);
  let _ = AP.join a0 _ in
  noop ()
  );
  return len0

#pop-options

let intro_singleton
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse p a va)
    (fun va' -> aparse (parse_list p) a va')
    (AP.length (array_of va) > 0)
    (fun va' ->
      array_of' va' == array_of' va /\
      va'.contents == [va.contents]
    )
= let vb = elim_aparse p a in
  parse_list_eq p (AP.contents_of vb);
  parse_list_eq p (Seq.slice (AP.contents_of vb) (AP.length (AP.array_of vb)) (AP.length (AP.array_of vb)));
  intro_aparse (parse_list p) a

inline_for_extraction
let read_replace
  (#t: _)
  (#p: _)
  (#v: Ghost.erased t)
  (r: R.ref t)
: ST t
    (R.pts_to r p v)
    (fun res -> R.pts_to r p res)
    True
    (fun res -> Ghost.reveal v == res)
= let res = R.read r in
  noop (); // necessary since FStarLang/FStar#2639
  return res

let list_fold_left_snoc
  (#a #b: Type)
  (f: a -> b -> Tot a)
  (init: a)
  (l1: list b)
  (x: b)
: Lemma
  (List.Tot.fold_left f init (l1 `List.Tot.append` [x]) == f (List.Tot.fold_left f init l1) x)
= List.Tot.fold_left_append f l1 [x]

let list_append_cons_r
  (#a: Type)
  (l1: list a)
  (x: a)
  (l2: list a)
: Lemma
  (l1 `List.Tot.append` (x :: l2) == (l1 `List.Tot.append` [x]) `List.Tot.append` l2)
= List.Tot.append_assoc l1 [x] l2

let intro_aparse_list_nil (#opened: _) (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array)
: STGhost (vl t) opened
    emp
    (fun res -> aparse_list p a res)
    True
    (fun res -> res.contents == [])
= let res : vl t = {
    array = None;
    contents = [];
    prf = ();
  }
  in
  rewrite emp (aparse_list p a res);
  res

let intro_aparse_list_cons (#opened: _) (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array) (w: v parse_list_kind (list t))
: STGhost (vl t) opened
    (aparse (parse_list p) a w)
    (fun res -> aparse_list p a res)
    (Cons? w.contents)
    (fun res ->
      Ghost.reveal res.array == Some (array_of' w) /\
      w == v_of_vl res /\
      res.contents == w.contents
    )
= let res = {
    array = Some (array_of' w);
    contents = w.contents;
    prf = ();
  }
  in
  rewrite (aparse (parse_list p) a w) (aparse_list p a res);
  res

let elim_aparse_list_nil (#opened: _) (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array) (w: vl t)
: STGhost unit opened
    (aparse_list p a w)
    (fun _ -> emp)
    (Nil? w.contents)
    (fun _ -> None? w.array)
= rewrite (aparse_list p a w) emp

let elim_aparse_list_cons (#opened: _) (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array) (w: vl t)
: STGhost (v parse_list_kind (list t)) opened
    (aparse_list p a w)
    (fun res -> aparse (parse_list p) a res)
    (Cons? w.contents)
    (fun res ->
      Ghost.reveal w.array == Some (array_of' res) /\
      res == v_of_vl w /\
      res.contents == w.contents
    )
= let res = v_of_vl w in
  rewrite (aparse_list p a w) (aparse (parse_list p) a res);
  res

let intro_aparse_list
  #opened #k #t p #wl #wr al ar
= let _ = ghost_is_cons p ar in
  if Nil? wr.contents
  then begin
    let _ = elim_nil p ar in
    let wl' = AP.join al ar in
    assert (AP.contents_of' wl' `Seq.equal` AP.contents_of' wl);
    let _ = intro_aparse_list_nil p ar in
    ()
  end else begin
    let _ = intro_aparse_list_cons p ar _ in
    ()
  end

#push-options "--z3rlimit 16"

let list_split_nil_l
  #opened #k #t p #va a
= let _ = elim_aparse (parse_list p) a in
  let ar = AP.gsplit a SZ.zero_size in
  let _ = gen_elim () in
  let va' = intro_aparse (parse_list p) ar in
  rewrite (aparse (parse_list p) ar va') (aparse (parse_list p) a va');
  intro_aparse_list p a a;
  let _ = gen_elim () in
  let _ = intro_nil p a in
  ()

#pop-options

let ghost_is_cons_opt
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (Ghost.erased bool) opened
    (aparse_list p a va)
    (fun _ -> aparse_list p a va)
    True
    (fun res ->
      (Ghost.reveal res == (length_opt va.array > 0)) /\
      (Ghost.reveal res == Cons? va.contents)
    )
= if Nil? va.contents
  then begin
    noop ();
    Ghost.hide false
  end else begin
    let _ = elim_aparse_list_cons p a _ in
    let res = ghost_is_cons p a in
    let _ = intro_aparse_list_cons p a _ in
    rewrite (aparse_list p a _) (aparse_list p a va);
    res
  end

let elim_aparse_list
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#wl: v parse_list_kind (list t))
  (#wr: _)
  (al ar: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_list p) al wl `star` aparse_list p ar wr)
    (fun w -> aparse (parse_list p) al w)
    (adjacent_opt (array_of' wl) wr.array /\
      k.parser_kind_subkind == Some ParserStrong)
    (fun w ->
      merge_opt_into (array_of' wl) wr.array (array_of' w) /\
      w.contents == wl.contents `List.Tot.append` wr.contents
    )
= if Nil? wr.contents
  then begin
    List.Tot.append_l_nil wl.contents;
    elim_aparse_list_nil p ar _;
    wl
  end else begin
    let _ = elim_aparse_list_cons p ar _ in
    let res = list_append p al ar in
    res
  end

inline_for_extraction
let elim_cons_opt_with_length
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va1: v k t)
  (#va2: v _ _)
  (a: byte_array)
  (len1: SZ.size_t)
  (a2: Ghost.erased byte_array)
: ST byte_array
    (aparse p a va1 `star` aparse (parse_list p) a2 va2)
    (fun a2' -> exists_ (fun (va1': v k t) -> exists_ (fun va2' ->
      aparse p a va1' `star`
      aparse_list p a2' va2' `star` pure (
      AP.adjacent (array_of' va1) (array_of' va2) /\
      merge_opt_into (array_of va1') va2'.array (AP.merge (array_of' va1) (array_of' va2)) /\
      va1'.contents == va1.contents /\
      va2'.contents == va2.contents /\
      AP.length (array_of' va1) == AP.length (array_of' va1') /\
      AP.length (array_of' va2) == length_opt va2'.array
    ))))
    (k.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of' va1) (array_of' va2) /\
      SZ.size_v len1 == AP.length (array_of va1)
    )
    (fun _ -> True)
= let _ = elim_aparse p a in
  let a2' = hop_arrayptr_aparse (parse_list p) a len1 a2 in
  intro_aparse_list p a a2';
  let _ = gen_elim () in
  let _ = intro_aparse p a in
  return a2'
