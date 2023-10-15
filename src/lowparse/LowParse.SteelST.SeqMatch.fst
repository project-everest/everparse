module LowParse.SteelST.SeqMatch
include Steel.ST.SeqMatch
include LowParse.SteelST.VCList
open Steel.ST.GenElim

module Seq = FStar.Seq
module GR = Steel.ST.GhostReference
module R = Steel.ST.Reference
module A = Steel.ST.Array
module AP = LowParse.SteelST.ArrayPtr
module SZ = FStar.SizeT
module W = LowParse.SteelST.L2ROutput

(* Going between `seq_list_match` and `seq_seq_match` *)

let rec list_index_append_cons
  (#t: Type)
  (l1: list t)
  (a: t)
  (l2: list t)
: Lemma
  (ensures (let l = l1 `List.Tot.append` (a :: l2) in
    let n1 = List.Tot.length l1 in
    n1 < List.Tot.length l /\
    List.Tot.index l n1 == a
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | a1 :: l1' -> list_index_append_cons l1' a l2

(* Computing the serialized list size *)

[@@__reduce__]
let array_payload_as_list_size_invariant0
  (#t: Type)
  (#t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (va: Ghost.erased (Seq.seq t))
  (vl: Ghost.erased (list t'))
  (a0: A.array t)
  (pi: perm)
  (sz: SZ.t)
  (perr: R.ref bool)
  (pl1 pl2: GR.ref (list t'))
  (pn: R.ref SZ.t)
  (psz: R.ref SZ.t)
  (cont: bool)
: Tot vprop
= A.pts_to a0 pi va `star`
  seq_list_match va vl item_match `star`
  exists_ (fun l1 -> exists_ (fun l2 -> exists_ (fun n -> exists_ (fun err -> exists_ (fun sz' ->
    GR.pts_to pl1 full_perm l1 `star`
    GR.pts_to pl2 full_perm l2 `star`
    R.pts_to pn full_perm n `star`
    R.pts_to perr full_perm err `star`
    R.pts_to psz full_perm sz' `star`
    pure (
      SZ.v n0 == List.Tot.length vl /\
      Ghost.reveal vl == l1 `List.Tot.append` l2 /\
      List.Tot.length l1 == SZ.v n /\
      SZ.v sz' + Seq.length (serialize (serialize_list _ s) l1) == SZ.v sz /\
      (err == true ==> Seq.length (serialize (serialize_list _ s) vl) > SZ.v sz) /\
      (cont == (not err && SZ.v n < SZ.v n0))
  ))))))

let array_payload_as_list_size_invariant
  (#t: Type)
  (#t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (va: Ghost.erased (Seq.seq t))
  (vl: Ghost.erased (list t'))
  (a0: A.array t)
  (pi: perm)
  (sz: SZ.t)
  (perr: R.ref bool)
  (pl1 pl2: GR.ref (list t'))
  (pn: R.ref SZ.t)
  (psz: R.ref SZ.t)
  (cont: bool)
: Tot vprop
= array_payload_as_list_size_invariant0 s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz cont

let item_size_post
  (#t': Type)
  (#k: parser_kind)
  (#p: parser k t')
  (s: serializer p)
  (y: t')
  (sz: SZ.t)
  (err: bool)
  (res: SZ.t)
: Tot prop
=
  let len = Seq.length (serialize s y) in
  if err then len > SZ.v sz else SZ.v res + len == SZ.v sz

#push-options "--split_queries always --z3cliopt smt.arith.nl=false --z3rlimit 256"
#restart-solver

inline_for_extraction
let array_payload_as_list_size_body
  (#t: Type0)
  (#t': Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (size: (
    (x: t) ->
    (y: Ghost.erased t') ->
    (sz: SZ.t) ->
    (perr: R.ref bool) ->
    STT SZ.t
      (R.pts_to perr full_perm false `star` item_match x y)
      (fun res -> item_match x y `star` exists_ (fun err -> R.pts_to perr full_perm err `star` pure (
        item_size_post s y sz err res
      )))
  ))
  (n0: SZ.t)
  (va: Ghost.erased (Seq.seq t))
  (vl: Ghost.erased (list t'))
  (a0: A.array t)
  (pi: perm)
  (sz: SZ.t)
  (perr: R.ref bool)
  (pl1 pl2: GR.ref (list t'))
  (pn: R.ref SZ.t)
  (psz: R.ref SZ.t)
  ()
: STT unit
    (array_payload_as_list_size_invariant s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz true)
    (fun _ -> exists_ (array_payload_as_list_size_invariant s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz))
= 
  rewrite
    (array_payload_as_list_size_invariant s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz true)
    (array_payload_as_list_size_invariant0 s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz true);
  let _ = gen_elim () in
  A.pts_to_length a0 _;
  seq_list_match_length item_match _ _;
  let n = R.read pn in
  [@@inline_let]
  let n' = SZ.add n 1sz in
  let l1 = GR.read pl1 in
  let l2 = GR.read pl2 in
  List.Tot.append_length l1 l2;
  serialize_list_append _ s l1 l2;
  let _ : squash (Cons? l2) = () in
  list_index_append_cons l1 (List.Tot.hd l2) (List.Tot.tl l2);
  List.Tot.append_assoc l1 [List.Tot.hd l2] (List.Tot.tl l2);
  serialize_list_cons _ s (List.Tot.hd l2) (List.Tot.tl l2);
  serialize_list_singleton _ s (List.Tot.hd l2);
  serialize_list_append _ s l1 [List.Tot.hd l2];
  noop ();
  let x = A.index a0 n in
  let _ = seq_list_match_index item_match _ _ (SZ.v n) in
  vpattern_rewrite_with_implies (fun x -> item_match x _) x;
  implies_trans
    (item_match _ _)
    (item_match _ _)
    (seq_list_match _ _ item_match);
  vpattern_rewrite (R.pts_to perr full_perm) false;
  let sz1 = R.read psz in
  let sz2 = size _ _ sz1 perr in
  let _ = gen_elim () in
  elim_implies
    (item_match x (List.Tot.index vl (SZ.v n)))
    (seq_list_match va vl item_match);
  let err = R.read perr in
  r_write_if (not err) pn n';
  r_write_if (not err) psz sz2;
  GR.write pl1 (if err then l1 else l1 `List.Tot.append` [List.Tot.hd l2]);
  GR.write pl2 (if err then l2 else List.Tot.tl l2);
  rewrite
    (array_payload_as_list_size_invariant0 s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz (not err && SZ.v n' < SZ.v n0))
    (array_payload_as_list_size_invariant s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz (not err && SZ.v n' < SZ.v n0));
  noop ();
  return ()

#pop-options

#push-options "--split_queries always --z3cliopt smt.arith.nl=false --z3rlimit 64"
#restart-solver

inline_for_extraction
let array_payload_as_list_size
  (#t: Type)
  (#t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (size: (
    (x: t) ->
    (y: Ghost.erased t') ->
    (sz: SZ.t) ->
    (perr: R.ref bool) ->
    STT SZ.t
      (R.pts_to perr full_perm false `star` item_match x y)
      (fun res -> item_match x y `star` exists_ (fun err -> R.pts_to perr full_perm err `star` pure (
        let len = Seq.length (serialize s y) in
        if err then len > SZ.v sz else SZ.v res + len == SZ.v sz
      )))
  ))
  (n0: SZ.t)
  (#va: Ghost.erased (Seq.seq t))
  (#vl: Ghost.erased (list t'))
  (#pi: perm)
  (a0: A.array t)
  (sz: SZ.t)
  (perr: R.ref bool)
: ST SZ.t
    (R.pts_to perr full_perm false `star` A.pts_to a0 pi va `star` seq_list_match va vl item_match)
    (fun res -> A.pts_to a0 pi va `star` seq_list_match va vl item_match `star` exists_ (fun err -> R.pts_to perr full_perm err `star` pure (
      let len = Seq.length (serialize (serialize_list p s) vl) in
      if err then len > SZ.v sz else SZ.v res + len == SZ.v sz
    )))
    (SZ.v n0 == A.length a0)
    (fun _ -> True)
= A.pts_to_length a0 _;
  seq_list_match_length item_match _ _;
  GR.with_local [] (fun (pl1: GR.ref (list t')) ->
  GR.with_local (Ghost.reveal vl) (fun (pl2: GR.ref (list t')) ->
  R.with_local 0sz (fun pn ->
  R.with_local sz (fun psz ->
    serialize_list_nil _ s;
    noop ();
    rewrite
      (array_payload_as_list_size_invariant0 s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz (0 < SZ.v n0))
      (array_payload_as_list_size_invariant s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz (0 < SZ.v n0));
    Steel.ST.Loops.while_loop
      (array_payload_as_list_size_invariant s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz)
      (fun _ ->
        let gcont = elim_exists () in
        rewrite
          (array_payload_as_list_size_invariant s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz gcont)
          (array_payload_as_list_size_invariant0 s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz gcont);
        let _ = gen_elim () in
        let n = R.read pn in
        let err = R.read perr in
        [@@inline_let]
        let cont = not err && n `SZ.lt` n0 in
        noop ();
        rewrite
          (array_payload_as_list_size_invariant0 s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz cont)
          (array_payload_as_list_size_invariant s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz cont);
        return cont
      )
      (array_payload_as_list_size_body s item_match size n0 va vl a0 pi sz perr pl1 pl2 pn psz);
    rewrite
      (array_payload_as_list_size_invariant s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz false)
      (array_payload_as_list_size_invariant0 s item_match n0 va vl a0 pi sz perr pl1 pl2 pn psz false);
    let _ = gen_elim () in
    let l1 = GR.read pl1 in
    let l2 = GR.read pl2 in
    let sz' = R.read psz in
    List.Tot.append_length l1 l2;
    List.Tot.append_l_nil l1;
    noop ();
    return sz'
  ))))

#pop-options

(* Serializing an array into a large enough left-to-right output buffer *)

[@@__reduce__]
let l2r_write_array_payload_as_list_invariant0
  (#t: Type)
  (#t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (va: Ghost.erased (Seq.seq t))
  (vl: Ghost.erased (list t'))
  (a0: A.array t)
  (pi: perm)
  (out0: byte_array)
  (vout: AP.array byte)
  (out: W.t)
  (pl2: GR.ref (list t'))
  (pn: R.ref SZ.t)
  (cont: bool)
: Tot vprop
= A.pts_to a0 pi va `star`
  seq_list_match va vl item_match `star`
  exists_ (fun vl1 -> exists_ (fun va2 -> exists_ (fun l2 -> exists_ (fun n ->
    aparse (parse_list p) out0 vl1 `star`
    W.vp out va2 `star`
    GR.pts_to pl2 full_perm l2 `star`
    R.pts_to pn full_perm n `star`
    pure (
      SZ.v n0 == List.Tot.length vl /\
      Ghost.reveal vl == vl1.contents `List.Tot.append` l2 /\
      List.Tot.length vl1.contents == SZ.v n /\
      AP.merge_into (array_of vl1) va2 vout /\
      Seq.length (serialize (serialize_list _ s) l2) <= AP.length va2 /\
      (cont == (SZ.v n < SZ.v n0))
  )))))

let l2r_write_array_payload_as_list_invariant
  (#t: Type)
  (#t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (va: Ghost.erased (Seq.seq t))
  (vl: Ghost.erased (list t'))
  (a0: A.array t)
  (pi: perm)
  (out0: byte_array)
  (vout: AP.array byte)
  (out: W.t)
  (pl2: GR.ref (list t'))
  (pn: R.ref SZ.t)
  (cont: bool)
: Tot vprop
= l2r_write_array_payload_as_list_invariant0 s item_match n0 va vl a0 pi out0 vout out pl2 pn cont

#push-options "--split_queries always --z3cliopt smt.arith.nl=false --z3rlimit 256"
#restart-solver

inline_for_extraction
let l2r_write_array_payload_as_list_body
  (#t: Type)
  (#t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (write: (
    (x: t) ->
    (y: Ghost.erased t') ->
    (#vout: AP.array byte) ->
    (out: W.t) ->
    ST byte_array
      (item_match x y `star` W.vp out vout)
      (fun res -> item_match x y `star` exists_ (fun vres -> exists_ (fun vout' ->
        aparse p res vres `star`
        W.vp out vout' `star`
        pure (
          AP.merge_into (array_of vres) vout' vout /\
          Ghost.reveal y == vres.contents
      ))))
      (Seq.length (serialize s y) <= AP.length vout)
      (fun _ -> True)
  ))
  (n0: SZ.t)
  (va: Ghost.erased (Seq.seq t))
  (vl: Ghost.erased (list t'))
  (a0: A.array t)
  (pi: perm)
  (out0: byte_array)
  (vout: AP.array byte)
  (out: W.t)
  (pl2: GR.ref (list t'))
  (pn: R.ref SZ.t)
  ()
: STT unit
    (l2r_write_array_payload_as_list_invariant s item_match n0 va vl a0 pi out0 vout out pl2 pn true)
    (fun _ -> exists_ (l2r_write_array_payload_as_list_invariant s item_match n0 va vl a0 pi out0 vout out pl2 pn))
= rewrite
    (l2r_write_array_payload_as_list_invariant s item_match n0 va vl a0 pi out0 vout out pl2 pn true)
    (l2r_write_array_payload_as_list_invariant0 s item_match n0 va vl a0 pi out0 vout out pl2 pn true);
  let _ = gen_elim () in
  A.pts_to_length a0 _;
  seq_list_match_length item_match _ _;
  let vl1 = vpattern (aparse (parse_list p) out0) in
  let l2 = GR.read pl2 in
  List.Tot.append_length vl1.contents l2;
  let _ : squash (Cons? l2) = () in
  list_index_append_cons vl1.contents (List.Tot.hd l2) (List.Tot.tl l2);
  List.Tot.append_assoc vl1.contents [List.Tot.hd l2] (List.Tot.tl l2);
  serialize_list_cons _ s (List.Tot.hd l2) (List.Tot.tl l2);
  noop ();
  let n = R.read pn in
  [@@inline_let]
  let n' = n `SZ.add` 1sz in
  let x = A.index a0 n in
  let _ = seq_list_match_index item_match _ _ (SZ.v n) in
  vpattern_rewrite_with_implies (fun x -> item_match x _) x;
  implies_trans
    (item_match _ _)
    (item_match _ _)
    (seq_list_match _ _ item_match);
  let out1 = write x _ out in
  let _ = gen_elim () in
  elim_implies
    (item_match x (List.Tot.index vl (SZ.v n)))
    (seq_list_match va vl item_match);
  aparse_serialized_length s out1;
  let _ = intro_singleton p out1 in
  let _ = list_append p out0 out1 in
  R.write pn n';
  GR.write pl2 (List.Tot.tl l2);
  rewrite
    (l2r_write_array_payload_as_list_invariant0 s item_match n0 va vl a0 pi out0 vout out pl2 pn (SZ.v n' < SZ.v n0))
    (l2r_write_array_payload_as_list_invariant s item_match n0 va vl a0 pi out0 vout out pl2 pn (SZ.v n' < SZ.v n0));
  return ()

#pop-options

#push-options "--split_queries always --z3cliopt smt.arith.nl=false --z3rlimit 64"
#restart-solver

inline_for_extraction
let l2r_write_array_payload_as_list
  (#t: Type)
  (#t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (write: (
    (x: t) ->
    (y: Ghost.erased t') ->
    (#vout: AP.array byte) ->
    (out: W.t) ->
    ST byte_array
      (item_match x y `star` W.vp out vout)
      (fun res -> item_match x y `star` exists_ (fun vres -> exists_ (fun vout' ->
        aparse p res vres `star`
        W.vp out vout' `star`
        pure (
          AP.merge_into (array_of vres) vout' vout /\
          Ghost.reveal y == vres.contents
      ))))
      (Seq.length (serialize s y) <= AP.length vout)
      (fun _ -> True)
  ))
  (n0: SZ.t)
  (#va: Ghost.erased (Seq.seq t))
  (#vl: Ghost.erased (list t'))
  (#pi: perm)
  (a0: A.array t)
  (#vout: AP.array byte)
  (out: W.t)
: ST byte_array
    (A.pts_to a0 pi va `star`
      seq_list_match va vl item_match `star`
      W.vp out vout
    )
    (fun res ->
      A.pts_to a0 pi va `star`
      seq_list_match va vl item_match `star`
      exists_ (fun vres -> exists_ (fun vout' ->
        aparse (parse_list p) res vres `star`
        W.vp out vout' `star`
        pure (
          AP.merge_into (array_of vres) vout' vout /\
          Ghost.reveal vl == vres.contents
    ))))
    (Seq.length (serialize (serialize_list _ s) vl) <= AP.length vout /\
      SZ.v n0 == A.length a0
    )
    (fun _ -> True)
= A.pts_to_length a0 _;
  seq_list_match_length item_match _ _;
  let out0 = W.split out 0sz in
  let _ = gen_elim () in
  let _ = intro_nil p out0 in
  GR.with_local (Ghost.reveal vl) (fun pl2 ->
  R.with_local 0sz (fun pn ->
    noop ();
    rewrite
      (l2r_write_array_payload_as_list_invariant0 s item_match n0 va vl a0 pi out0 vout out pl2 pn (0 < SZ.v n0))
      (l2r_write_array_payload_as_list_invariant s item_match n0 va vl a0 pi out0 vout out pl2 pn (0 < SZ.v n0));
    Steel.ST.Loops.while_loop
      (l2r_write_array_payload_as_list_invariant s item_match n0 va vl a0 pi out0 vout out pl2 pn)
      (fun _ ->
        let gcont = elim_exists () in
        rewrite
          (l2r_write_array_payload_as_list_invariant s item_match n0 va vl a0 pi out0 vout out pl2 pn gcont)
          (l2r_write_array_payload_as_list_invariant0 s item_match n0 va vl a0 pi out0 vout out pl2 pn gcont);
        let _ = gen_elim () in
        let n = R.read pn in
        [@@inline_let]
        let cont = n `SZ.lt` n0 in
        noop ();
        rewrite
          (l2r_write_array_payload_as_list_invariant0 s item_match n0 va vl a0 pi out0 vout out pl2 pn cont)
          (l2r_write_array_payload_as_list_invariant s item_match n0 va vl a0 pi out0 vout out pl2 pn cont);
        return cont
      )
      (l2r_write_array_payload_as_list_body s item_match write n0 va vl a0 pi out0 vout out pl2 pn);
    rewrite
      (l2r_write_array_payload_as_list_invariant s item_match n0 va vl a0 pi out0 vout out pl2 pn false)
      (l2r_write_array_payload_as_list_invariant0 s item_match n0 va vl a0 pi out0 vout out pl2 pn false);
    let _ = gen_elim () in
    let vl1 = vpattern (aparse (parse_list p) out0) in
    let l2 = GR.read pl2 in
    List.Tot.append_length vl1.contents l2;
    assert (Nil? l2);
    List.Tot.append_l_nil vl1.contents;
    noop ();
    return out0
  ))

#pop-options

inline_for_extraction
let array_payload_as_nlist_size
  (#t: Type)
  (#t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (size: (
    (x: t) ->
    (y: Ghost.erased t') ->
    (sz: SZ.t) ->
    (perr: R.ref bool) ->
    STT SZ.t
      (R.pts_to perr full_perm false `star` item_match x y)
      (fun res -> item_match x y `star` exists_ (fun err -> R.pts_to perr full_perm err `star` pure (
        let len = Seq.length (serialize s y) in
        if err then len > SZ.v sz else SZ.v res + len == SZ.v sz
      )))
  ))
  (#va: Ghost.erased (Seq.seq t))
  (#vl: Ghost.erased (list t'))
  (n0: SZ.t {
    SZ.v n0 == List.Tot.length vl
  })
  (#pi: perm)
  (a0: A.array t)
  (sz: SZ.t)
  (perr: R.ref bool)
: STT SZ.t
    (R.pts_to perr full_perm false `star` A.pts_to a0 pi va `star` seq_list_match va vl item_match)
    (fun res -> A.pts_to a0 pi va `star` seq_list_match va vl item_match `star` exists_ (fun err -> R.pts_to perr full_perm err `star` pure (
      let len = Seq.length (serialize (serialize_nlist (SZ.v n0) s) vl) in
      if err then len > SZ.v sz else SZ.v res + len == SZ.v sz
    )))
= serialize_nlist_serialize_list (SZ.v n0) s vl;
  seq_list_match_length item_match _ _;
  A.pts_to_length a0 _;
  let res = array_payload_as_list_size s item_match size n0 a0 sz perr in
  let _ = gen_elim () in
  return res

inline_for_extraction
let l2r_write_array_payload_as_nlist
  (#t: Type)
  (#t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (s: serializer p {
    serialize_list_precond k
  })
  (item_match: t -> t' -> vprop)
  (write: (
    (x: t) ->
    (y: Ghost.erased t') ->
    (#vout: AP.array byte) ->
    (out: W.t) ->
    ST byte_array
      (item_match x y `star` W.vp out vout)
      (fun res -> item_match x y `star` exists_ (fun vres -> exists_ (fun vout' ->
        aparse p res vres `star`
        W.vp out vout' `star`
        pure (
          AP.merge_into (array_of vres) vout' vout /\
          Ghost.reveal y == vres.contents
      ))))
      (Seq.length (serialize s y) <= AP.length vout)
      (fun _ -> True)
  ))
  (#va: Ghost.erased (Seq.seq t))
  (#vl: Ghost.erased (list t'))
  (#pi: perm)
  (n0: SZ.t)
  (a0: A.array t)
  (#vout: AP.array byte)
  (out: W.t)
: ST byte_array
    (A.pts_to a0 pi va `star`
      seq_list_match va vl item_match `star`
      W.vp out vout
    )
    (fun res ->
      A.pts_to a0 pi va `star`
      seq_list_match va vl item_match `star`
      exists_ (fun vres -> exists_ (fun vout' ->
        aparse (parse_nlist (SZ.v n0) p) res vres `star`
        W.vp out vout' `star`
        pure (
          AP.merge_into (array_of vres) vout' vout /\
          Ghost.reveal vl == vres.contents
    ))))
    (SZ.v n0 == List.Tot.length vl /\
      Seq.length (serialize (serialize_nlist (SZ.v n0) s) vl) <= AP.length vout
    )
    (fun _ -> True)
= serialize_nlist_serialize_list (SZ.v n0) s vl;
  seq_list_match_length item_match _ _;
  A.pts_to_length a0 _;
  let res = l2r_write_array_payload_as_list s item_match write n0 a0 out in
  let _ = gen_elim () in
  let _ = aparse_list_aparse_nlist p (SZ.v n0) res in
  return res

(* Parsing into an array

While this implementation also works if the low-level value type is a pointer type, the resulting C code may not be idiomatic. Also, it assumes that the parsing function for elements always succeeds (e.g. in the case of an array of pointers, `alloc` never returns NULL.)

*)

noextract
unfold
let read_array_payload_invariant_prop0
  (#t: Type)
  (#t': Type)
  (k: parser_kind)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (cont: bool)
  (s: Seq.seq t)
  (l1: list t')
  (vr: v parse_list_kind (list t'))
  (n: SZ.t)
  (n': nat)
: Tot prop
=
      k.parser_kind_subkind == Some ParserStrong /\
      SZ.v n0 == List.Tot.length vl0.contents /\
      SZ.v n == List.Tot.length l1 /\
      Seq.length s == SZ.v n0 /\
      List.Tot.append l1 vr.contents == vl0.contents /\
      n' == SZ.v n /\
      (cont == true <==> (SZ.v n < SZ.v n0))

noextract
let read_array_payload_invariant_prop
  (#t #t': Type)
  (k: parser_kind)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (cont: bool)
  (s: Seq.seq t)
  (l1: list t')
  (vr: v parse_list_kind (list t'))
  (n: SZ.t)
  (n': nat)
: Tot prop
= read_array_payload_invariant_prop0 k n0 vl0 cont s l1 vr n n'

[@@__reduce__]
let read_array_payload_invariant_body0
  (#t #t': Type)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (s: Seq.seq t)
  (l1: list t')
  (r: byte_array)
  (vr: v parse_list_kind (list t'))
  (n: SZ.t)
  (n': nat)
: Tot vprop
=
    A.pts_to a0 full_perm s `star`
    R.pts_to pn full_perm n `star`
    R.pts_to pr full_perm r `star`
    seq_seq_match item_match s (Seq.seq_of_list vl0.contents) 0 n' `star`
    aparse (parse_list p) r vr `star`
    ((seq_seq_match item_match s (Seq.seq_of_list vl0.contents) 0 n' `star` aparse (parse_list p) r vr) `implies_`
      aparse (parse_list p) l0 vl0)

[@@erasable]
noeq
type read_array_payload_invariant_t (t t': Type) = {
  s: Seq.seq t;
  l1: list t';
  r: byte_array;
  vr: v parse_list_kind (list t');
  n: SZ.t;
  n': nat;
}

[@@__reduce__]
let read_array_payload_invariant0
  (#t #t': Type)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (cont: bool)
: Tot vprop
= exists_ (fun w ->
    read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr w.s w.l1 w.r w.vr w.n w.n' `star`
    pure (read_array_payload_invariant_prop k n0 vl0 cont w.s w.l1 w.vr w.n w.n')
  )

let read_array_payload_invariant
  (#t #t': Type)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (cont: bool)
: Tot vprop
= read_array_payload_invariant0 p item_match n0 vl0 l0 a0 pn pr cont

let intro_read_array_payload_invariant
  (#t #t': Type)
  (#opened: _)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (l1: list t')
  (cont: bool)
  (s: Seq.seq t)
  (r: byte_array)
  (vr: v parse_list_kind (list t'))
  (n: SZ.t)
  (n': nat)
: STGhost unit opened
    (read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr s l1 r vr n n')
    (fun _ -> read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr cont)
    (read_array_payload_invariant_prop0 k n0 vl0 cont s l1 vr n n')
    (fun _ -> True)
= let w : read_array_payload_invariant_t t t' = {
    s = s;
    l1 = l1;
    r = r;
    vr = vr;
    n = n;
    n' = n';
  }
  in
  rewrite
    (read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr s l1 r vr n n')
    (read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr w.s w.l1 w.r w.vr w.n w.n');
  rewrite
    (read_array_payload_invariant0 p item_match n0 vl0 l0 a0 pn pr cont)  
    (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr cont)  

let elim_read_array_payload_invariant
  (#t #t': Type)
  (#opened: _)
  (#k: parser_kind)
  (p: parser k t')
  (item_match: t -> t' -> vprop)
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (cont: bool)
: STGhost (read_array_payload_invariant_t t t') opened
    (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr cont)
    (fun w -> read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr w.s w.l1 w.r w.vr w.n w.n')
    True
    (fun w -> read_array_payload_invariant_prop k n0 vl0 cont w.s w.l1 w.vr w.n w.n')
= rewrite
    (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr cont)
    (read_array_payload_invariant0 p item_match n0 vl0 l0 a0 pn pr cont);
  let _ = gen_elim () in
  vpattern_replace (fun w -> read_array_payload_invariant_body0 p item_match n0 vl0 l0 a0 pn pr w.s w.l1 w.r w.vr w.n w.n')

let list_append_length_lt
  (#t: Type)
  (l0: list t)
  (n0: SZ.t)
  (sq0': squash (SZ.v n0 == List.Tot.length l0))
  (l1: list t)
  (n: SZ.t)
  (sq1': squash (SZ.v n == List.Tot.length l1))
  (l2: list t)
  (sq0: squash (l1 `List.Tot.append` l2 == l0))
  (sq1: squash (SZ.v n < SZ.v n0))
: Tot (squash (Cons? l2))
= List.Tot.append_length l1 l2

let implies_trans_cut
  (#opened: _)
  (p q1 q2 r2 r3: vprop)
: STGhostT unit opened
    ((p @==> (q1 `star` q2)) `star` ((q2 `star` r2) @==> r3))
    (fun _ -> (p `star` r2) @==> (q1 `star` r3))
= implies_reg_l q1 (q2 `star` r2) r3;
  implies_with_tactic ((q1 `star` q2) `star` r2) (q1 `star` (q2 `star` r2));
  implies_trans ((q1 `star` q2) `star` r2) (q1 `star` (q2 `star` r2)) (q1 `star` r3);
  implies_trans_l1 p (q1 `star` q2) r2 (q1 `star` r3)

#push-options "--split_queries always --z3cliopt smt.arith.nl=false --z3rlimit 64"
#restart-solver

inline_for_extraction noextract let
read_array_payload_body
  (#t: Type0)
  (#t': Type0)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (j: jumper p)
  (item_match: t -> t' -> vprop)
  (read: (
    (#va: v k t') ->
    (a: byte_array) ->
    (alen: SZ.t) ->
    ST t
    (aparse p a va)
    (fun c' ->
      item_match c' va.contents `star`
      (item_match c' va.contents `implies_` aparse p a va)
    )
    (alen == AP.len (array_of va))
    (fun _ -> True)
  ))
  (n0: SZ.t)
  (vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (a0: A.array t)
  (pn: R.ref SZ.t)
  (pr: R.ref byte_array)
  (_: unit)
: STT unit
    (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr true)
    (fun _ -> exists_ (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr))
= let w = elim_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr true in // +6
  A.pts_to_length a0 _;
  let vr_cons: squash (Cons? w.vr.contents) = list_append_length_lt vl0.contents n0 () w.l1 w.n () w.vr.contents () () in
  let r = R.read pr in
  vpattern_rewrite_with_implies (fun r -> aparse (parse_list p) r _) r; // +5
  let gr' = ghost_elim_cons_with_implies p r in // +4.2
  let _ = gen_elim () in
  let sz = get_parsed_size j r in
  let r' = hop_aparse_aparse_with_size_with_implies p (parse_list p) r sz gr' in // +4.1
  implies_trans_r1 // +4 -4.1 -4.2
    (aparse p r _) // q1
    (aparse (parse_list p) r' _) // p
    (aparse (parse_list p) gr' _) // q2
    (aparse (parse_list p) r _); // r
  let v1 = vpattern (aparse p r) in
  let vr' = vpattern (aparse (parse_list p) r') in
  List.Tot.append_assoc w.l1 [v1.contents] vr'.contents;
  List.Tot.append_length w.l1 [v1.contents];
  list_index_append_cons w.l1 v1.contents vr'.contents;
  let l1' : Ghost.erased (list t') = Ghost.hide (w.l1 `List.Tot.append` [v1.contents]) in
  R.write pr r';
  let n = R.read pn in
  let _ : squash (SZ.v n < Seq.length w.s) = () in
  let n' = n `SZ.add` 1sz in
  let n'_as_nat : Ghost.erased nat = SZ.v n' in
  R.write pn n';
  let c = read r sz in // +3
  A.upd a0 n c;
  let s' = vpattern_replace_erased (A.pts_to a0 full_perm) in
  seq_seq_match_weaken_with_implies // +2
    item_match w.s s' (Seq.seq_of_list vl0.contents) (Seq.seq_of_list vl0.contents) 0 w.n';
  rewrite_with_implies // +1
    (item_match c _)
    (seq_seq_match_item item_match s' (Seq.seq_of_list vl0.contents) (SZ.v n));
  on_range_snoc_with_implies // +0
    (seq_seq_match_item item_match s' (Seq.seq_of_list vl0.contents))
    _ _ (SZ.v n) n'_as_nat;
  (* BEGIN FIXME: this should be automated away *)
  implies_trans_r2 // -0 -1
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat)
    (seq_seq_match item_match _ _ _ _)
    (seq_seq_match_item item_match _ _ _)
    (item_match c _);
  implies_trans_l2 // -2
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat)
    (seq_seq_match item_match _ _ _ _)
    (item_match c _)
    (seq_seq_match item_match _ _ _ _);
  implies_trans_r2 // -3
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat)
    (seq_seq_match item_match _ _ _ _)
    (item_match c _)
    (aparse p _ _);
  implies_trans_cut // -4
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat) // p
    (seq_seq_match item_match _ _ _ _) // q1
    (aparse p _ _) // q2
    (aparse (parse_list p) _ _) // r2
    (aparse (parse_list p) _ _); // r3
  implies_trans_r2 // -5
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat `star` aparse (parse_list p) _ _)
    (seq_seq_match item_match _ _ _ _)
    (aparse (parse_list p) _ _)
    (aparse (parse_list p) _ _);
  implies_trans // -6
    (seq_seq_match item_match s' (Seq.seq_of_list vl0.contents) 0 n'_as_nat `star` aparse (parse_list p) _ _)
    (seq_seq_match item_match _ _ _ _ `star` aparse (parse_list p) _ _)
    (aparse (parse_list p) _ _);
  (* END FIXME *)
  intro_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr l1' (n' `SZ.lt` n0) _ _ _ _ _;
  return ()

#pop-options

inline_for_extraction
let read_array_payload_from_list
  (#t #t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (j: jumper p)
  (item_match: t -> t' -> vprop)
  (read: (
    (#va: v k t') ->
    (a: byte_array) ->
    (alen: SZ.t) ->
    ST t
    (aparse p a va)
    (fun c' ->
      item_match c' va.contents `star`
      (item_match c' va.contents `implies_` aparse p a va)
    )
    (alen == AP.len (array_of va))
    (fun _ -> True)
  ))
  (n0: SZ.t)
  (#vl0: v parse_list_kind (list t'))
  (l0: byte_array)
  (#va0: Ghost.erased (Seq.seq t))
  (a0: A.array t)
: ST (Ghost.erased (Seq.seq t))
    (A.pts_to a0 full_perm va0 `star`
      aparse (parse_list p) l0 vl0
    )
    (fun res ->
      A.pts_to a0 full_perm res `star`
      seq_list_match res vl0.contents item_match `star`
      (seq_list_match res vl0.contents item_match `implies_`
        aparse (parse_list p) l0 vl0
      )
    )
    (A.length a0 == SZ.v n0 /\
      List.Tot.length vl0.contents == SZ.v n0 /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
= A.pts_to_length a0 _;
  on_range_empty
    (seq_seq_match_item item_match va0 (Seq.seq_of_list vl0.contents))
    0 0;
  intro_implies
    (seq_seq_match item_match va0 (Seq.seq_of_list vl0.contents) 0 0 `star`
      aparse (parse_list p) l0 vl0)
    (aparse (parse_list p) l0 vl0)
    emp
    (fun _ -> drop (seq_seq_match item_match _ _ _ _));
  R.with_local 0sz (fun pn ->
  R.with_local l0 (fun pr ->
    intro_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr [] (0sz `SZ.lt` n0) _ _ _ _ _;
    Steel.ST.Loops.while_loop
      (read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr)
      (fun _ ->
        let gcont = elim_exists () in
        let w = elim_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr gcont in
        let n = R.read pn in
        [@@inline_let]
        let cont = n `SZ.lt` n0 in
        intro_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr w.l1 cont _ _ _ _ _;
        return cont
      )
      (read_array_payload_body j item_match read n0 vl0 l0 a0 pn pr);
    let w = elim_read_array_payload_invariant p item_match n0 vl0 l0 a0 pn pr false in
    List.Tot.append_length w.l1 w.vr.contents;
    assert (Nil? w.vr.contents);
    List.Tot.append_l_nil w.l1;
    A.pts_to_length a0 _;
    rewrite_with_implies
      (seq_seq_match item_match _ _ _ _)
      (seq_seq_match item_match w.s (Seq.seq_of_list vl0.contents) 0 (List.Tot.length vl0.contents));
    seq_seq_match_seq_list_match_with_implies item_match _ vl0.contents;
    implies_trans
      (seq_list_match w.s vl0.contents item_match)
      (seq_seq_match item_match _ _ _ _)
      (seq_seq_match item_match _ _ _ _);
    implies_concl_r
      (seq_list_match w.s vl0.contents item_match)
      (seq_seq_match item_match _ _ _ _)
      (aparse (parse_list p) _ _);
    implies_trans
      (seq_list_match w.s vl0.contents item_match)
      (seq_seq_match item_match _ _ _ _ `star` aparse (parse_list p) _ _)
      (aparse (parse_list p) _ _);
    return (Ghost.hide w.s)
  ))

inline_for_extraction
let read_array_payload_from_nlist
  (#t #t': Type)
  (#k: Ghost.erased parser_kind)
  (#p: parser k t')
  (j: jumper p)
  (item_match: t -> t' -> vprop)
  (read: (
    (#va: v k t') ->
    (a: byte_array) ->
    (alen: SZ.t) ->
    ST t
    (aparse p a va)
    (fun c' ->
      item_match c' va.contents `star`
      (item_match c' va.contents `implies_` aparse p a va)
    )
    (alen == AP.len (array_of va))
    (fun _ -> True)
  ))
  (n0: SZ.t)
  (#vl0: v (parse_nlist_kind (SZ.v n0) k) (nlist (SZ.v n0) t'))
  (l0: byte_array)
  (#va0: Ghost.erased (Seq.seq t))
  (a0: A.array t)
: ST (Ghost.erased (Seq.seq t))
    (A.pts_to a0 full_perm va0 `star`
      aparse (parse_nlist (SZ.v n0) p) l0 vl0
    )
    (fun res ->
      A.pts_to a0 full_perm res `star`
      seq_list_match res vl0.contents item_match `star`
      (seq_list_match res vl0.contents item_match `implies_`
        aparse (parse_nlist (SZ.v n0) p) l0 vl0
      )
    )
    (A.length a0 == SZ.v n0 /\
      k.parser_kind_low > 0 /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
= A.pts_to_length a0 _;
  let vl = aparse_nlist_aparse_list_with_implies p (SZ.v n0) l0 in
  let res = read_array_payload_from_list j item_match read n0 l0 a0 in
  rewrite_with_implies
    (seq_list_match _ vl.contents item_match)
    (seq_list_match _ vl0.contents item_match);
  implies_trans
    (seq_list_match _ _ item_match)
    (seq_list_match _ _ item_match)
    (aparse (parse_list p) _ _);
  implies_trans
    (seq_list_match _ _ item_match)
    (aparse (parse_list p) _ _)
    (aparse (parse_nlist (SZ.v n0) p) _ _);
  return res
