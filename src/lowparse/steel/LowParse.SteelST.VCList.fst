module LowParse.SteelST.VCList
include LowParse.SteelST.List.Base
include LowParse.SteelST.Parse // to shadow the vl vs. v operators from List
include LowParse.Spec.VCList
open Steel.ST.GenElim

module AP = LowParse.SteelST.ArrayPtr

let aparse_nlist_aparse_list
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n: nat)
  (#va: v (parse_nlist_kind n k) (nlist n t))
  (a: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_nlist n p) a va)
    (fun va' -> aparse (parse_list p) a va')
    (k.parser_kind_low > 0)
    (fun va' ->
      array_of va' == array_of va /\
      va'.contents == (va.contents <: list t)
    )
= let b = elim_aparse _ a in
  parse_nlist_parse_list_full p n (AP.contents_of b);
  intro_aparse _ a

let aparse_list_aparse_nlist
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n: nat)
  (#va: v parse_list_kind (list t))
  (a: byte_array)
: STGhost (v (parse_nlist_kind n k) (nlist n t)) opened
    (aparse (parse_list p) a va)
    (fun va' -> aparse (parse_nlist n p) a va')
    (n == List.Tot.length va.contents)
    (fun va' ->
      array_of' va' == array_of' va /\
      (va'.contents <: list t) == va.contents
    )
= let b = elim_aparse _ a in
  parse_list_parse_nlist p (AP.contents_of b);
  intro_aparse _ a

let aparse_nlist_aparse_list_with_implies
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (n: nat)
  (#va: v (parse_nlist_kind n k) (nlist n t))
  (a: byte_array)
: STGhost (v parse_list_kind (list t)) opened
    (aparse (parse_nlist n p) a va)
    (fun va' -> aparse (parse_list p) a va' `star` (aparse (parse_list p) a va' `implies_` aparse (parse_nlist n p) a va))
    (k.parser_kind_low > 0)
    (fun va' ->
      va'.contents == (va.contents <: list t)
    )
= let va' = aparse_nlist_aparse_list p n a in
  intro_implies
    (aparse (parse_list p) a va')
    (aparse (parse_nlist n p) a va)
    emp
    (fun _ ->
      let _ = aparse_list_aparse_nlist p n a in
      vpattern_rewrite (aparse (parse_nlist n p) a) va
    );
  va'

let intro_nlist_nil
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (p: parser k t)
  (#va: _)
  (a: byte_array)
: STGhost (v (parse_nlist_kind n k) (nlist n t)) opened
    (AP.arrayptr a va)
    (fun va' -> aparse (parse_nlist n p) a va')
    (AP.length (AP.array_of va) == 0 /\
      n == 0
    )
    (fun va' ->
      array_of va' == AP.array_of va /\
      va'.contents == []
    )
= parse_nlist_zero p (AP.contents_of va);
  intro_aparse (parse_nlist n p) a

let elim_nlist_nil
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (p: parser k t)
  (#va: v (parse_nlist_kind n k) (nlist n t))
  (a: byte_array)
: STGhost (AP.v byte) opened
    (aparse (parse_nlist n p) a va)
    (fun va' -> AP.arrayptr a va')
    (n == 0 \/ Nil? va.contents)
    (fun va' ->
      n == 0 /\
      Nil? va.contents /\
      array_of va == AP.array_of va' /\
      AP.length (AP.array_of va') == 0
    )
= let va' = elim_aparse (parse_nlist n p) a in
  parse_nlist_zero p (AP.contents_of va');
  noop ();
  va'

#push-options "--z3rlimit 16"

let intro_nlist_cons
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (n': nat)
  (p: parser k t)
  (n: nat)
  (#va1: v _ _)
  (#va2: v _ _)
  (a1 a2: byte_array)
: STGhost (v (parse_nlist_kind n' k) (nlist n' t)) opened
    (aparse p a1 va1 `star` aparse (parse_nlist n p) a2 va2)
    (fun va -> aparse (parse_nlist n' p) a1 va)
    (k.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of va1) (array_of va2) /\
      n' == n + 1
    )
    (fun va ->
      n' == n + 1 /\
      AP.merge_into (array_of' va1) (array_of' va2) (array_of' va) /\
      va.contents == va1.contents :: va2.contents
    )
= let vb1 = elim_aparse _ a1 in
  let vb2 = elim_aparse _ a2 in
  let vb = AP.join a1 a2 in
  parse_strong_prefix p (AP.contents_of vb1) (AP.contents_of vb);
  parse_nlist_eq n' p (AP.contents_of vb);
  assert (AP.contents_of vb2 `Seq.equal` Seq.slice (AP.contents_of vb) (AP.length (AP.array_of vb1)) (AP.length (AP.array_of vb)));
  noop ();
  intro_aparse (parse_nlist n' p) a1

#pop-options

let intro_nlist_cons_with
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (n': nat)
  (p: parser k t)
  (n: nat)
  (#va1: v _ _)
  (#va2: v _ _)
  (a1 a2: byte_array)
  (va: v (parse_nlist_kind n' k) (nlist n' t))
: STGhost unit opened
    (aparse p a1 va1 `star` aparse (parse_nlist n p) a2 va2)
    (fun _ -> aparse (parse_nlist n' p) a1 va)
    (k.parser_kind_subkind == Some ParserStrong /\
      AP.merge_into (array_of' va1) (array_of' va2) (array_of' va) /\
      va.contents == va1.contents :: va2.contents /\
      n' == n + 1
    )
    (fun _ -> True)
= let _ = intro_nlist_cons n' p n a1 a2 in
  vpattern_rewrite (aparse _ a1) va

let list_length_cons
  (#t: Type)
  (a: t)
  (q: list t)
: Lemma
  (List.Tot.length (a :: q) == 1 + List.Tot.length q)
= ()

let list_length_cons_n
  (#t: Type)
  (a: t)
  (q: list t)
  (n: nat)
  (n_pred: nat)
: Lemma
  (requires (List.Tot.length (a :: q) == n /\
    n == n_pred + 1))
  (ensures (List.Tot.length q == n_pred))
= ()

let elim_nlist_cons_post
  (k: parser_kind)
  (t: Type0)
  (n n_pred: nat)
  (va1: v k t) (va2: v (parse_nlist_kind n_pred k) (nlist n_pred t))
  (va: v (parse_nlist_kind n k) (nlist n t))
: GTot prop
=
      n == n_pred + 1 /\
      AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
      va.contents == va1.contents :: va2.contents

#push-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false"

#restart-solver
let elim_nlist_cons
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (n: nat)
  (n_pred: nat)
  (#va: v _ _)
  (a: byte_array)
: STGhost (Ghost.erased byte_array) opened
    (aparse (parse_nlist n p) a va)
    (fun a2 -> exists_ (fun (va1: v _ _) -> exists_ (fun (va2: v _ _) ->
      aparse p a va1 `star`
      aparse (parse_nlist n_pred p) a2 va2 `star` pure (
      elim_nlist_cons_post k t n n_pred va1 va2 va
    ))))
    (Cons? va.contents /\
      n == n_pred + 1 /\
      k.parser_kind_subkind == Some ParserStrong)
    (fun _ -> True)
= let vb = elim_aparse _ a in
  parse_nlist_eq n p (AP.contents_of vb);
  let a2 = ghost_peek_strong p a in
  let _ = gen_elim () in
  let va1 = vpattern_replace (aparse p a) in
  let va2 = intro_aparse (parse_nlist n_pred p) a2 in
  noop ();
  a2

#pop-options

let intro_nlist_one
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (#va: v k t)
  (a: byte_array)
  (n: nat)
: STGhost (v (parse_nlist_kind n k) (nlist n t)) opened
    (aparse p a va)
    (fun va' -> aparse (parse_nlist n p) a va')
    (n == 1)
    (fun va' ->
      array_of' va' == array_of' va /\
      va'.contents == [va.contents]
    )
= let vb = elim_aparse p a in
  parse_nlist_one p (AP.contents_of vb);
  noop ();
  intro_aparse (parse_nlist n p) a

let elim_nlist_one
  (#opened: _)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (n: nat)
  (#va: v (parse_nlist_kind n k) (nlist n t))
  (a: byte_array)
: STGhost (v k t) opened
    (aparse (parse_nlist n p) a va)
    (fun va' -> aparse p a va')
    (n == 1)
    (fun va' ->
      array_of' va' == array_of' va /\
      va.contents == [va'.contents]
    )
= let vb = elim_aparse (parse_nlist n p) a in
  parse_nlist_one p (AP.contents_of vb);
  noop ();
  intro_aparse p a

let rec intro_nlist_sum
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (p: parser k t)
  (n1: nat)
  (#va1: v (parse_nlist_kind n1 k) (nlist n1 t))
  (a1: byte_array)
  (n2: nat)
  (#va2: v (parse_nlist_kind n2 k) (nlist n2 t))
  (a2: byte_array)
: STGhost (v (parse_nlist_kind n k) (nlist n t)) opened
    (aparse (parse_nlist n1 p) a1 va1 `star` aparse (parse_nlist n2 p) a2 va2)
    (fun va' -> aparse (parse_nlist n p) a1 va')
    (AP.adjacent (array_of' va1) (array_of' va2) /\
      n == n1 + n2 /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun va' ->
      AP.merge_into (array_of' va1) (array_of' va2) (array_of' va') /\
      va'.contents == va1.contents `List.Tot.append` va2.contents
    )
    (decreases n1)
= if n1 = 0
  then begin
    let va1' = elim_nlist_nil n1 p a1 in
    let va2' = elim_aparse (parse_nlist n2 p) a2 in
    let va' = AP.join a1 a2 in
    assert (AP.contents_of va' `Seq.equal` AP.contents_of va2');
    noop ();
    intro_aparse (parse_nlist n p) a1
  end else begin
    noop ();
    let n1' : nat = n1 - 1 in
    let n' : nat = n - 1 in
    let a1' = elim_nlist_cons p n1 n1' a1 in
    let _ = gen_elim () in
    let _ = intro_nlist_sum n' p n1' a1' n2 a2 in
    let res = intro_nlist_cons n p n' a1 a1' in
    res
  end

let elim_nlist_sum_post
  (t: Type)
  (k: parser_kind)
  (n n1 n2: nat)
  (va1: v (parse_nlist_kind n1 k) (nlist n1 t))
  (va2: v (parse_nlist_kind n2 k) (nlist n2 t))
  (va: v (parse_nlist_kind n k) (nlist n t))
: GTot prop
=
        n == n1 + n2 /\
        AP.merge_into (array_of' va1) (array_of' va2) (array_of' va) /\
        va.contents == va1.contents `List.Tot.append` va2.contents

#push-options "--z3rlimit 16"

#restart-solver
let rec elim_nlist_sum
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (n: nat)
  (p: parser k t)
  (#va: v (parse_nlist_kind n k) (nlist n t))
  (a: byte_array)
  (n1 n2: nat)
: STGhost (Ghost.erased byte_array) opened
    (aparse (parse_nlist n p) a va)
    (fun ar -> exists_ (fun va1 -> exists_ (fun va2 ->
      aparse (parse_nlist n1 p) a va1 `star` aparse (parse_nlist n2 p) ar va2 `star`
      pure (elim_nlist_sum_post t k n n1 n2 va1 va2 va)
    )))
    (
      n == n1 + n2 /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun _ -> True)
    (decreases n1)
=
  if n1 = 0
  then begin
    let va = elim_aparse (parse_nlist n p) a in
    let ar = AP.gsplit a 0sz in
    let _ = gen_elim () in
    let vr = vpattern_replace (AP.arrayptr ar) in
    assert (AP.contents_of' vr `Seq.equal` AP.contents_of' va);
    let _ = intro_nlist_nil n1 p a in
    let _ = intro_aparse (parse_nlist n2 p) ar in
    noop ();
    ar
  end else begin
    let n1' : nat = n1 - 1 in
    let n' : nat = n - 1 in
    let a' = elim_nlist_cons p n n' a in
    let _ = gen_elim () in
    let ar = elim_nlist_sum n' p a' n1' n2 in
    let _ = gen_elim () in
    let _ = intro_nlist_cons n1 p n1' a a' in
    noop ();
    ar
  end

#pop-options

let aparse_nlist_count_le_size
  (k: parser_kind)
  (t: Type)
  (n: nat)
  (va: v (parse_nlist_kind n k) (nlist n t))
: Lemma
  (requires (k.parser_kind_low > 0))
  (ensures (n <= AP.length (array_of' va)))
= ()

