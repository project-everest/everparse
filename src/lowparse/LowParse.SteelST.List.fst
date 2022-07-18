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

module R = Steel.ST.Reference

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

module U32 = FStar.UInt32

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

module L = Steel.ST.Loops

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
  let plen = R.alloc SZ.zero_size in
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
  R.free plen;
  noop ();
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

module P = Steel.FractionalPermission

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

let merge_opt_into_r
  (a1: AP.array byte)
  (a2: option (AP.array byte))
  (a3: AP.array byte)
  (a2': AP.array byte)
  (a21: AP.array byte)
  (a22: option (AP.array byte))
: Lemma
  (requires (
    merge_opt_into a1 a2 a3 /\
    a2 == Some a2' /\
    merge_opt_into a21 a22 a2'
  ))
  (ensures (
    AP.adjacent a1 a21 /\
    merge_opt_into (AP.merge a1 a21) a22 a3 
  ))
= ()

#set-options "--ide_id_info_off"

#push-options "--z3rlimit 64"

#restart-solver
inline_for_extraction
let list_iter_gen_body
  (#k: parser_kind)
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

#push-options "--z3rlimit 32"

#restart-solver
inline_for_extraction
let list_iter_gen
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
=
  let afull = compute_afull enable_arrays va al in
  let pa = R.alloc a in
  let plen = R.alloc len in
  let paccu = R.alloc init in
  let pcont = R.alloc (len <> SZ.zero_size) in
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
  R.free pcont;
  R.free paccu;
  R.free plen;
  R.free pa;
  return res

#pop-options

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
    SZ.size_v len == AP.length (array_of' wl) /\
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
  (plen: R.ref SZ.size_t)
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
  (plen: R.ref SZ.size_t)
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
    STT SZ.size_t
      (aparse p a va `star` AP.arrayptr out vout)
      (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
        aparse p' out vout' `star` AP.arrayptr res' vres' `star` pure (
        SZ.size_v res == AP.length (array_of vout') /\
        SZ.size_v res > 0 /\
        AP.merge_into (array_of' vout') (AP.array_of vres') (AP.merge (AP.array_of vout) (array_of' va)) /\
        vout'.contents == Ghost.reveal phi va.contents
      )))))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.size_t { SZ.size_v len == length_opt va.array })
  (#vout: _)
  (out: byte_array { adjacent_opt (AP.array_of vout) va.array })  // TODO: add write permissions
: STT SZ.size_t
    (aparse_list p a va `star` AP.arrayptr out vout)
    (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
      aparse (parse_list p') out vout' `star` AP.arrayptr res' vres' `star` pure (
      SZ.size_v res == AP.length (array_of' vout') /\
      AP.merge_into (array_of' vout') (AP.array_of vres') (merge_opt (AP.array_of vout) va.array) /\
      vout'.contents == List.Tot.map phi va.contents
    )))))
= let al0 = AP.array_of vout in
  let afull = merge_opt al0 va.array in
  let out1 = AP.split out SZ.zero_size in
  let _ = gen_elim () in
  let _ = intro_nil p' out in
  let plen = R.alloc SZ.zero_size in
  let pout = R.alloc out1 in
  rewrite
    (list_map_inplace_le_opt_state0 p' phi out pout plen al0 () [])
    (list_map_inplace_le_opt_state p' phi out pout plen al0 () []);
  list_iter_consumes_with_array
    j
    (fun _ _ -> ())
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
      let len' = SZ.size_add len len1 in
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
  R.free pout;
  R.free plen;
  return res

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
    STT SZ.size_t
      (aparse p a va `star` AP.arrayptr out vout)
      (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
        aparse p' out vout' `star` AP.arrayptr res' vres' `star` pure (
        SZ.size_v res == AP.length (array_of vout') /\
        SZ.size_v res > 0 /\
        AP.merge_into (array_of' vout') (AP.array_of vres') (AP.merge (AP.array_of vout) (array_of' va)) /\
        vout'.contents == Ghost.reveal phi va.contents
      )))))
  ))
  (#va: _)
  (a: byte_array)
  (len: SZ.size_t { SZ.size_v len == AP.length (array_of' va) })
  (#vout: _)
  (out: byte_array { AP.adjacent (AP.array_of vout) (array_of' va) })  // TODO: add write permissions
: STT SZ.size_t
    (aparse (parse_list p) a va `star` AP.arrayptr out vout)
    (fun res -> exists_ (fun res' -> exists_ (fun vres' -> exists_ (fun (vout': v _ _) ->
      aparse (parse_list p') out vout' `star` AP.arrayptr res' vres' `star` pure (
      SZ.size_v res == AP.length (array_of' vout') /\
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
  (len: SZ.size_t)
: ST (v _ _)
    (aparse (parse_list p) a va)
    (fun va' -> aparse (parse_list p') a va')
    (SZ.size_v len == AP.length (array_of' va))  // TODO: add write permissions
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
  noop ();
  rewrite
    (list_map_inplace_eq_state0 p' phi a al () [])
    (list_map_inplace_eq_state p' phi a al () []);
  list_iter_consumes_with_array
    j
    (fun _ _ -> ())
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
  (len: SZ.size_t)
: ST _
    (aparse_list p a va)
    (fun va' -> aparse_list p' a va')
    (SZ.size_v len == length_opt va.array)  // TODO: add write permissions
    (fun va' ->
      va'.array == va.array /\
      va'.contents == List.Tot.map phi va.contents
    )
= let _ = ghost_is_cons_opt p a in
  if len = SZ.zero_size
  then begin
    elim_aparse_list_nil p a _;
    intro_aparse_list_nil p' a
  end else begin
    let _ = elim_aparse_list_cons p a _ in
    let _ = list_map_inplace_eq j p' phi f a len in
    intro_aparse_list_cons p' a _
  end
