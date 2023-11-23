module LowParse.SteelST.List.Nth

open Steel.ST.GenElim

module L = Steel.ST.Loops
module R = Steel.ST.Reference

unfold
let list_split_state_prop0
  k
  (#t: Type)
  (va0: v parse_list_kind (list t))
  (i: SZ.t)
  (cont: bool)
  (n: SZ.t)
  (vl vr: v parse_list_kind (list t))
: Tot prop
=
  AP.merge_into (array_of' vl) (array_of' vr) (array_of' va0) /\
  List.Tot.length vl.contents == SZ.v n /\
  SZ.v n <= SZ.v i /\
  k.parser_kind_subkind == Some ParserStrong /\
  SZ.v i <= List.Tot.length va0.contents /\
  (cont == (SZ.v n < SZ.v i)) /\
  va0.contents == List.Tot.append vl.contents vr.contents

let list_split_state_prop
  k
  (#t: Type)
  (va0: v parse_list_kind (list t))
  (i: SZ.t)
  (cont: bool)
  (n: SZ.t)
  (vl vr: v parse_list_kind (list t))
: Tot prop
=
  list_split_state_prop0 k va0 i cont n vl vr

[@@__reduce__] // FIXME: WHY WHY WHY not honored under exists_ ?
let list_split_state1
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a0: byte_array)
  (bn: R.ref SZ.t)
  (be: R.ref byte_array)
  (bcont: R.ref bool)
  (cont: bool)
  (n: SZ.t)
  (vl: v parse_list_kind (list t))
  (e: byte_array)
  (vr: v parse_list_kind (list t))
: Tot vprop
= 
  R.pts_to bn full_perm n `star`
  aparse (parse_list p) a0 vl `star`
  R.pts_to be full_perm e `star`
  aparse (parse_list p) e vr `star`
  R.pts_to bcont full_perm cont

[@@__reduce__]
let list_split_state0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a0: byte_array)
  (va0: v parse_list_kind (list t))
  (i: SZ.t)
  (bn: R.ref SZ.t)
  (be: R.ref byte_array)
  (bcont: R.ref bool)
  (cont: bool)
: Tot vprop
= exists_ (fun (n: SZ.t) -> exists_ (fun (vl: v parse_list_kind (list t)) -> exists_ (fun (e: byte_array) -> exists_ (fun (vr: v parse_list_kind (list t)) ->
  R.pts_to bn full_perm n `star`
  aparse (parse_list p) a0 vl `star`
  R.pts_to be full_perm e `star`
  aparse (parse_list p) e vr `star`
  R.pts_to bcont full_perm cont
 // list_split_state1 p a0 bn be bcont cont n vl e vr  // FIXME: WHY WHY WHY is __reduce__ not honored here?
  `star`
    pure (
      list_split_state_prop k va0 i cont n vl vr
  )))))

let list_split_state
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a0: byte_array)
  (va0: v parse_list_kind (list t))
  (i: SZ.t)
  (bn: R.ref SZ.t)
  (be: R.ref byte_array)
  (bcont: R.ref bool)
  (cont: bool)
: Tot vprop
= list_split_state0 p a0 va0 i bn be bcont cont

let list_split_state_intro
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (a0: byte_array)
  (va0: v parse_list_kind (list t))
  (i: SZ.t)
  (bn: R.ref SZ.t)
  (be: R.ref byte_array)
  (bcont: R.ref bool)
  (cont: bool)
  (n: SZ.t)
  (vl: v parse_list_kind (list t))
  (e: byte_array)
  (vr: v parse_list_kind (list t))
: STGhost unit opened
    (list_split_state1 p a0 bn be bcont cont n vl e vr)
    (fun _ -> list_split_state p a0 va0 i bn be bcont cont)
    (list_split_state_prop0 k va0 i cont n vl vr)
    (fun _ -> True)
= noop ();
  rewrite
    (list_split_state0 p a0 va0 i bn be bcont cont)
    (list_split_state p a0 va0 i bn be bcont cont)

let list_append_is_cons_r
  (#t: Type)
  (l1 l2: list t)
: Lemma
  (requires (List.Tot.length l1 < List.Tot.length (l1 `List.Tot.append` l2)))
  (ensures (Cons? l2))
= List.Tot.append_length l1 l2

#push-options "--z3rlimit 16"
#restart-solver

inline_for_extraction
let list_split_test
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (p: parser k t)
  (a0: byte_array)
  (va0: v parse_list_kind (list t))
  (i: SZ.t)
  (bn: R.ref SZ.t)
  (be: R.ref byte_array)
  (bcont: R.ref bool)
  ()
: STT bool
     (exists_ (list_split_state p a0 va0 i bn be bcont))
     (fun cont -> list_split_state p a0 va0 i bn be bcont cont)
=
        let gcont = elim_exists () in
        rewrite
          (list_split_state p a0 va0 i bn be bcont gcont)
          (list_split_state0 p a0 va0 i bn be bcont gcont);
        let _ = gen_elim () in
        let cont = read_replace bcont in
        rewrite
          (list_split_state0 p a0 va0 i bn be bcont cont)
          (list_split_state p a0 va0 i bn be bcont cont);
        return cont

#pop-options

#push-options "--z3rlimit 128"
#restart-solver

inline_for_extraction
let list_split_body
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (a0: byte_array)
  (va0: v parse_list_kind (list t))
  (i: SZ.t)
  (bn: R.ref SZ.t)
  (be: R.ref byte_array)
  (bcont: R.ref bool)
  ()
: STT unit
     (list_split_state p a0 va0 i bn be bcont true)
     (fun _ -> exists_ (list_split_state p a0 va0 i bn be bcont))
=
  rewrite
    (list_split_state p a0 va0 i bn be bcont true)
    (list_split_state0 p a0 va0 i bn be bcont true);
  let _ = gen_elim () in
  let ge = vpattern_replace_erased (fun e -> R.pts_to be full_perm e `star` aparse (parse_list p) e _) in
  let ve : v _ _ = vpattern_replace (aparse (parse_list p) ge) in
  let e = R.read be in
  rewrite (aparse (parse_list p) ge _) (aparse (parse_list p) e ve);
  let va : v _ _ = vpattern_replace (aparse (parse_list p) a0) in
  list_append_is_cons_r va.contents ve.contents;
  let e' = elim_cons j e in
  let _ = gen_elim () in
  let ve' : v _ _ = vpattern_replace (aparse (parse_list p) e') in
  let ve1 = intro_singleton p e in
  List.Tot.append_assoc va.contents ve1.contents ve'.contents;
  List.Tot.append_length va.contents ve1.contents;
  assert (List.Tot.length ve1.contents == 1);
  assert (ve.contents == ve1.contents `List.Tot.append` ve'.contents);
  noop ();
  let va' = list_append p a0 e in
  let n = R.read bn in
  let n' = SZ.add n 1sz in
  let cont' = (n' `SZ.lt` i) in
  R.write bn n';
  R.write bcont cont';
  R.write be e';
  list_split_state_intro p a0 va0 i bn be bcont cont' n' va' e' ve';
  return ()

#pop-options

#push-options "--z3rlimit 64"
#restart-solver

inline_for_extraction
let list_split
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#va0: v _ _)
  (a0: byte_array)
  (i: SZ.t)
: ST byte_array
    (aparse (parse_list p) a0 va0)
    (fun e -> exists_ (fun (vl: v _ _) -> exists_ (fun (vr: v _ _) ->
      aparse (parse_list p) a0 vl `star`
      aparse (parse_list p) e vr  `star`
      pure (
        List.Tot.length vl.contents == SZ.v i /\
        va0.contents == vl.contents `List.Tot.append` vr.contents /\
        AP.merge_into (array_of' vl) (array_of' vr) (array_of' va0)
      )
    )))
    (k.parser_kind_subkind == Some ParserStrong /\
      SZ.v i <= List.Tot.length va0.contents
    )
    (fun _ -> True)
= let _ = elim_aparse (parse_list p) a0 in
  let e = AP.split a0 0sz in
  let _ = gen_elim () in
  let va1 = intro_nil p a0 in
  let ve0 : v _ _ = intro_aparse (parse_list p) e in
  List.Tot.append_nil_l ve0.contents;
  let cont = 0sz `SZ.lt` i in
  with_local cont (fun bcont ->
  with_local 0sz (fun bn ->
  with_local e (fun be ->
    noop ();
    list_split_state_intro p a0 va0 i bn be bcont cont 0sz va1 e ve0;
    L.while_loop
      (list_split_state p a0 va0 i bn be bcont)
      (list_split_test p a0 va0 i bn be bcont)
      (list_split_body j a0 va0 i bn be bcont);
    rewrite
      (list_split_state p a0 va0 i bn be bcont false)
      (list_split_state0 p a0 va0 i bn be bcont false);
    let _ = gen_elim () in
    let e = R.read be in
    vpattern_rewrite (fun e -> R.pts_to be full_perm e `star` aparse (parse_list p) e _) e;
    return e
  )))

#pop-options

let rec list_index_eq
  (#t: Type)
  (ll: list t)
  (x: t)
  (lr: list t)
: Lemma
  (ensures (
    let i = List.Tot.length ll in
    let l = ll `List.Tot.append` (x :: lr) in
    i < List.Tot.length l /\
    List.Tot.index l i == x
  ))
  (decreases ll)
= match ll with
  | [] -> ()
  | a :: q -> list_index_eq q x lr

#push-options "--z3rlimit 32"
#restart-solver

inline_for_extraction
let list_nth
  (#k: Ghost.erased parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (#va0: v _ _)
  (a0: byte_array)
  (i: SZ.t)
: ST byte_array
    (aparse (parse_list p) a0 va0)
    (fun e -> exists_ (fun a -> exists_ (fun (vl: v _ _) -> exists_ (fun (ve: v _ _) -> exists_ (fun (vr: v _ _) ->
      aparse (parse_list p) a0 vl `star`
      aparse p e ve `star`
      aparse (parse_list p) (list_nth_tail a0 i e a) vr `star`
      pure (
        list_nth_post k va0 i vl ve vr
    ))))))
    (
      k.parser_kind_subkind == Some ParserStrong /\
      SZ.v i < List.Tot.length va0.contents
    )
    (fun _ -> True)
=
  let e = list_split j a0 i in
  let _ = gen_elim () in
  let vl : v _ _ = vpattern_replace (aparse (parse_list p) a0) in
  let ve0 : v _ _ = vpattern_replace (aparse (parse_list p) e) in
  list_append_is_cons_r vl.contents ve0.contents;
  let a = ghost_elim_cons p e in
  let _ = gen_elim () in
  let vr : v _ _ = vpattern_replace (aparse (parse_list p) a) in
  let ve : v _ _ = vpattern_replace (aparse p e) in
  list_index_eq vl.contents ve.contents vr.contents;
  noop ();
  rewrite
    (aparse (parse_list p) a _)
    (aparse (parse_list p) (list_nth_tail a0 i e a) vr);
  noop ();
  return e

#pop-options

let list_nth_restore
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (#vl: v parse_list_kind (list t))
  (#ve: v k t)
  (#vr: v parse_list_kind (list t))
  (#p: parser k t)
  (a0: byte_array)
  (va0: v _ _)
  (i: SZ.t)
  (e: byte_array)
  (a: byte_array)
: STGhost unit opened
    (
      aparse (parse_list p) a0 vl `star`
      aparse p e ve `star`
      aparse (parse_list p) (list_nth_tail a0 i e a) vr
    )
    (fun _ -> aparse (parse_list p) a0 va0)
    (list_nth_post k va0 i vl ve vr)
    (fun _ -> True)
= let _ = intro_cons p e (list_nth_tail a0 i e a) in
  let va0' = list_append _ a0 e in
  rewrite
    (aparse (parse_list p) a0 va0')
    (aparse (parse_list p) a0 va0)

