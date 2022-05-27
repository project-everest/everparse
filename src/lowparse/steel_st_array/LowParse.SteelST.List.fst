module LowParse.SteelST.List
include LowParse.Spec.List
include LowParse.SteelST.Validate
include LowParse.SteelST.Access

module AP = LowParse.SteelST.ArrayPtr

open Steel.ST.GenElim

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
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
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

module SZ = LowParse.Steel.StdInt

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

(*
#push-options "--z3rlimit 24"

// TODO: replace this recursive function with a loop
let rec list_iter'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#t': Type)
  (phi: Ghost.erased (t' -> t -> t'))
  (state: t' -> list t -> vprop)
  (f: (
    (#va: _) ->
    (a: byte_array) ->
    (accu: t') ->
    (l: Ghost.erased (list t)) ->
    STT t'
      (aparse p a va `star` state accu l)
      (fun res -> aparse p a va `star` state res (List.Tot.snoc (Ghost.reveal l, va.contents)) `star` pure (res == Ghost.reveal phi accu va.contents))
  ))
  (#l1: Ghost.erased (list t))
  (#va1: _)
  (a1: byte_array)
  (#va2: _)
  (a2: byte_array)
  (len: SZ.size_t)
  (init: t')
: ST t'
    (aparse (parse_list p) a1 va1 `star` aparse (parse_list p) a2 va2 `star` state init l1)
    (fun res -> exists_ (fun va -> aparse (parse_list p) a1 va `star` state res va.contents `star` pure (
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents `List.Tot.append` va2.contents /\
      res == List.Tot.fold_left (Ghost.reveal phi) init va2.contents
    )))
    (requires (
      k.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of va1) (array_of va2) /\
      SZ.size_v len == AP.length (array_of va2) /\
      Ghost.reveal l1 == va1.contents
    ))
    (ensures (fun _ -> True))
= let _ = ghost_is_cons p a2 in
  if len = SZ.zero_size
  then
  begin
    let va = list_append p a1 a2 in
    List.Tot.append_l_nil va1.contents;
    rewrite (state _ _) (state init va.contents);
    return init
  end
  else
  begin
    let a25 = elim_cons j a2 in
    let _ = gen_elim () in
    let sz = get_parsed_size j a2 in // FIXME: avoid calling j twice, we should have a version of hop_aparse_aparse taking a size instead
    rewrite (state _ _) (state init (Ghost.hide va1.contents));
    let accu = f a2 init (Ghost.hide va1.contents) in
    let _ = gen_elim () in
    let _ = intro_singleton p a2 in
    List.Tot.append_assoc va1.contents [List.Tot.hd va2.contents] (List.Tot.tl va2.contents);
    let va1' = list_append p a1 a2 in
    rewrite (state _ _) (state accu va1'.contents);
    let res = list_iter' j phi state f a1 a25 (len `SZ.size_sub` sz) accu in
    let _ = gen_elim () in
    return res
  end

#pop-options
*)

let array_opt = Ghost.erased (option (AP.array byte))

let length_opt (a: array_opt) : GTot nat =
  match Ghost.reveal a with
  | None -> 0
  | Some a' -> AP.length a'

let adjacent_opt (a1: AP.array byte) (a2: array_opt) : Tot prop =
  match Ghost.reveal a2 with
  | None -> True
  | Some a2' -> AP.adjacent a1 a2'

let merge_opt (a1: AP.array byte) (a2: array_opt) : Pure (AP.array byte)
  (requires (adjacent_opt a1 a2))
  (ensures (fun res -> AP.length res == AP.length a1 + length_opt a2))
= match Ghost.reveal a2 with
  | None -> a1
  | Some a2' -> AP.merge a1 a2'

let merge_opt_into (a1: AP.array byte) (a2: array_opt) (a3: AP.array byte) : Tot prop =
  adjacent_opt a1 a2 /\
  merge_opt a1 a2 == a3

let merge_opt_assoc (a1 a2: AP.array byte) (a3: array_opt) : Lemma
  (requires (
    (AP.adjacent a1 a2 /\ adjacent_opt a2 a3) \/
    (AP.adjacent a1 a2 /\ adjacent_opt (AP.merge a1 a2) a3) \/
    (adjacent_opt a2 a3 /\ AP.adjacent a1 (merge_opt a2 a3))
  ))
  (ensures (
    AP.adjacent a1 a2 /\ adjacent_opt (AP.merge a1 a2) a3 /\
    adjacent_opt a2 a3 /\ AP.adjacent a1 (merge_opt a2 a3) /\
    merge_opt (AP.merge a1 a2) a3 == AP.merge a1 (merge_opt a2 a3)
  ))
= ()

[@@erasable]
noeq
type vl (t: Type) = {
  array: array_opt;
  contents: list t;
  prf: squash (None? array == Nil? contents);
}

let v_of_vl (#t: Type) (w: vl t { Some? w.array }) : Tot (v parse_list_kind (list t)) = {
  array_perm = Some?.v w.array;
  contents = w.contents;
  array_perm_prf = ();
}

let aparse_list (#k: parser_kind) (#t: Type) (p: parser k t) (a: byte_array) (v: vl t) : Tot vprop =
  if None? v.array
  then emp
  else aparse (parse_list p) a (v_of_vl v)

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
    (fun _ -> True)
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
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#wl: _)
  (#wr: v parse_list_kind (list t))
  (al ar: byte_array)
: STGhost unit opened
    (AP.arrayptr al wl `star` aparse (parse_list p) ar wr)
    (fun _ -> exists_ (fun wl' -> exists_ (fun wr' ->
      AP.arrayptr al wl' `star`
      aparse_list p ar wr' `star` pure (
      AP.adjacent (AP.array_of wl) (array_of' wr) /\
      merge_opt_into (AP.array_of wl') wr'.array (AP.merge (AP.array_of wl) (array_of' wr)) /\
      AP.contents_of' wl' == AP.contents_of' wl /\
      AP.length (AP.array_of wl') == AP.length (AP.array_of wl) /\
      wr'.contents == wr.contents /\
      length_opt wr'.array == AP.length (array_of' wr)
    ))))
    (AP.adjacent (AP.array_of wl) (array_of' wr))
    (fun _ -> True)
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
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: v parse_list_kind (list t))
  (a: byte_array)
: STGhostT unit opened
    (aparse (parse_list p) a va)
    (fun _ -> exists_ (fun (va1: v parse_list_kind (list t)) -> exists_ (fun (va2: vl t) ->
      aparse (parse_list p) a va1 `star`
      aparse_list p a va2 `star` pure (
      merge_opt_into (array_of va1) va2.array (array_of va) /\
      length_opt va2.array == AP.length (array_of va) /\
      va1.contents == [] /\
      va2.contents == va.contents
    ))))
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

#push-options "--z3rlimit 16"

inline_for_extraction
let elim_cons_opt
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#va: _)
  (a: byte_array)
: ST byte_array
    (aparse_list p a va)
    (fun a2 -> exists_ (fun (va1: v k t) -> exists_ (fun va2 ->
      aparse p a va1 `star`
      aparse_list p a2 va2 `star` pure (
      Some? va.array /\
      merge_opt_into (array_of va1) va2.array (Some?.v va.array) /\
      va.contents == va1.contents :: va2.contents /\
      AP.length (array_of va1) > 0
    ))))
    (Cons? va.contents /\ k.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= let _ = elim_aparse_list_cons p a _ in
  let res = elim_cons j a in
  let _ = gen_elim () in
  let _ = elim_aparse p a in
  intro_aparse_list p a res;
  let _ = gen_elim () in
  let _ = intro_aparse p a in
  return res

#pop-options

assume val list_iter_gen
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
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

#set-options "--ide_id_info_off"

inline_for_extraction
let list_iter_consumes_with_array
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#t': Type)
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
        AP.merge_into al (array_of' va) al' /\
        l' == List.Tot.snoc (Ghost.reveal l, va.contents) /\
        res == Ghost.reveal phi accu va.contents
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
= let state0 x = match x with None -> (fun _ _ -> pure False) | Some x' -> state x' in
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

(*
admit_ ();
  return (magic ())

let gres = ghost_elim_cons p a in
  let _ = gen_elim () in
  let res = hop_aparse_aparse j (parse_list p) a gres in
  res


(*
let va' = elim_aparse (parse_list p) a in
  parse_list_eq p (AP.contents_of va');
  let a2 = AP.split a SZ.zero_size in
  let _ = gen_elim () in
  let _ = intro_aparse (parse_list p) a2 in
  let _ = intro_nil p a in
  return a2

let list_split_nil_l
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: v parse_list_kind (list t))
  (a: byte_array)
: STT byte_array
    (aparse (parse_list p) a va)
    (fun res -> exists_ (fun (va1: v parse_list_kind (list t)) -> exists_ (fun (va2: v parse_list_kind (list t)) ->
      aparse (parse_list p) a va1 `star`
      aparse (parse_list p) res va2 `star` pure (
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      AP.length (array_of va2) == AP.length (array_of va) /\
      va1.contents == [] /\
      va2.contents == va.contents
    ))))
= let va' = elim_aparse (parse_list p) a in
  parse_list_eq p (AP.contents_of va');
  let a2 = AP.split a SZ.zero_size in
  let _ = gen_elim () in
  let _ = intro_aparse (parse_list p) a2 in
  let _ = intro_nil p a in
  return a2


let list_iter_gen_prefix
  (#t: Type)
  (va: v parse_list_kind (list t))
  (ar: byte_array)
  (vr: v parse_list_kind (list t))
  (vl: v parse_list_kind (list t))
: Tot prop
= 
  AP.merge_into (array_of' vl) (array_of' vr) (array_of va) /\
  vl.contents == va.contents


(*
= let a2 = list_split_nil_l p a in
  let _ = gen_elim_dep () in // replacing with explicit elim_exists, elim_pure WILL NOT decrease rlimit
  let res = list_iter' j phi state f a a2 len init in
  let _ = gen_elim () in
  List.Tot.append_nil_l va.contents; // FIXME: WHY WHY WHY?
  rewrite (aparse (parse_list p) a _) (aparse (parse_list p) a va);
  rewrite (state _ _) (state res va.contents);
  return res
*)


let list_iter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#t': Type)
  (phi: Ghost.erased (t' -> t -> t'))
  (state: t' -> list t -> vprop)
  (f: (
    (#va: _) ->
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
    (aparse (parse_list p) a va `star` state init [])
    (fun res -> aparse (parse_list p) a va `star` state res va.contents)
    (SZ.size_v len == AP.length (array_of va) /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> res == List.Tot.fold_left (Ghost.reveal phi) init va.contents)
= let a2 = list_split_nil_l p a in
  let _ = gen_elim_dep () in // replacing with explicit elim_exists, elim_pure WILL NOT decrease rlimit
  let res = list_iter' j phi state f a a2 len init in
  let _ = gen_elim () in
  List.Tot.append_nil_l va.contents; // FIXME: WHY WHY WHY?
  rewrite (aparse (parse_list p) a _) (aparse (parse_list p) a va);
  rewrite (state _ _) (state res va.contents);
  return res

#pop-options
