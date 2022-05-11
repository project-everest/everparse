module LowParse.SteelST.List
include LowParse.Spec.List
include LowParse.SteelST.Validate
include LowParse.SteelST.Access

module AP = LowParse.SteelST.ArrayPtr

open Steel.ST.Util

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

#push-options "--z3rlimit 16"

// TODO: replace this recursive function with a loop
let rec list_iter'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (state: list t -> vprop)
  (f: (
    (#va: _) ->
    (a: byte_array) ->
    (l: Ghost.erased (list t)) ->
    STT unit
      (aparse p a va `star` state l)
      (fun _ -> aparse p a va `star` state (List.Tot.snoc (Ghost.reveal l, va.contents)))
  ))
  (#l1: Ghost.erased (list t))
  (#va1: _)
  (a1: byte_array)
  (#va2: _)
  (a2: byte_array)
  (len: SZ.size_t)
: ST (v parse_list_kind (list t))
    (aparse (parse_list p) a1 va1 `star` aparse (parse_list p) a2 va2 `star` state l1)
    (fun va -> aparse (parse_list p) a1 va `star` state va.contents)
    (requires (
      k.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of va1) (array_of va2) /\
      SZ.size_v len == AP.length (array_of va2) /\
      Ghost.reveal l1 == va1.contents
    ))
    (ensures (fun va ->
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents `List.Tot.append` va2.contents
    ))
= let _ = ghost_is_cons p a2 in
  if len = SZ.zero_size
  then
  begin
    let res = list_append p a1 a2 in
    List.Tot.append_l_nil va1.contents;
    rewrite (state _) (state res.contents);
    return res
  end
  else
  begin
    let a25 = elim_cons j a2 in
    let _ = gen_elim () in
    let sz = get_parsed_size j a2 in // FIXME: avoid calling j twice, we should have a version of hop_aparse_aparse taking a size instead
    rewrite (state _) (state (Ghost.hide va1.contents));
    f a2 (Ghost.hide va1.contents);
    let _ = intro_singleton p a2 in
    List.Tot.append_assoc va1.contents [List.Tot.hd va2.contents] (List.Tot.tl va2.contents);
    let va1' = list_append p a1 a2 in
    rewrite (state _) (state va1'.contents);
    let res = list_iter' j state f a1 a25 (len `SZ.size_sub` sz) in
    return res
  end

#pop-options

let list_split_nil_l
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STT byte_array
    (aparse (parse_list p) a va)
    (fun res -> exists_ (fun va1 -> exists_ (fun va2 ->
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

#push-options "--z3rlimit 24"

let list_iter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (state: list t -> vprop)
  (f: (
    (#va: _) ->
    (a: byte_array) ->
    (l: Ghost.erased (list t)) ->
    STT unit
      (aparse p a va `star` state l)
      (fun _ -> aparse p a va `star` state (List.Tot.snoc (Ghost.reveal l, va.contents)))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.size_t)
: ST unit
    (aparse (parse_list p) a va `star` state [])
    (fun _ -> aparse (parse_list p) a va `star` state va.contents)
    (SZ.size_v len == AP.length (array_of va) /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
= let a2 = list_split_nil_l p a in
  let _ = gen_elim () in // replacing with explicit elim_exists, elim_pure WILL NOT decrease rlimit
  let va' = list_iter' j state f a a2 len in
  // {assuming va' == va} will decrease rlimit to 16
  rewrite (aparse (parse_list p) a va') (aparse (parse_list p) a va);
  rewrite (state _) (state va.contents);
  return ()

#pop-options
