module LowParse.SteelST.VCList.Sorted
include LowParse.SteelST.VCList.Iterator
include LowParse.Spec.Sorted

module AP = LowParse.SteelST.ArrayPtr
module R = Steel.ST.Reference
module SZ = FStar.SizeT

open Steel.ST.GenElim

[@@erasable]
noeq
type nlist_sorted_invariant_t
  (k: parser_kind)
  (t: Type)
= {
    n2: SZ.t;
    a: byte_array;
    va: v (parse_nlist_kind (SZ.v n2 + 1) k) (nlist (SZ.v n2 + 1) t);
    va1: v k t;
    a2: byte_array;
    va2: v (parse_nlist_kind (SZ.v n2) k) (nlist (SZ.v n2) t);
    res: bool;
  }

let nlist_sorted_invariant_prop
  (k: parser_kind)
  (t: Type)
  (order: t -> t -> bool)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (n2: SZ.t)
  (va: v (parse_nlist_kind (SZ.v n2 + 1) k) (nlist (SZ.v n2 + 1) t))
  (va1: v k t)
  (va2: v (parse_nlist_kind (SZ.v n2) k) (nlist (SZ.v n2) t))
  (res: bool)
  (cont: bool)
: GTot prop
= AP.merge_into (array_of va1) (array_of va2) (array_of va) /\
  va.contents == va1.contents :: va2.contents /\
  List.Tot.sorted order va0.contents == (res && List.Tot.sorted order va.contents) /\
  cont == (res && (SZ.v n2 > 0)) /\
  k.parser_kind_subkind == Some ParserStrong

[@@__reduce__]
let nlist_sorted_invariant_body
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (order: t -> t -> bool)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn2: R.ref SZ.t)
  (pres: R.ref bool)
  (cont: bool)
  (w: nlist_sorted_invariant_t k t)
: Tot vprop
=
  R.pts_to pn2 full_perm w.n2 `star`
  nlist_iterator p n0 va0 a0 (SZ.v w.n2 + 1) w.va `star`
  R.pts_to pa full_perm w.a `star`
  aparse p w.a w.va1 `star`
  aparse (parse_nlist (SZ.v w.n2) p) w.a2 w.va2 `star`
  R.pts_to pres full_perm w.res

[@@__reduce__]
let nlist_sorted_invariant0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (order: t -> t -> bool)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn2: R.ref SZ.t)
  (pres: R.ref bool)
  (cont: bool)
: Tot vprop
= exists_ (fun (w: nlist_sorted_invariant_t k t) ->
    nlist_sorted_invariant_body p order n0 va0 a0 pa pn2 pres cont w `star`
    pure (nlist_sorted_invariant_prop k t order n0 va0 w.n2 w.va w.va1 w.va2 w.res cont)
  )

let nlist_sorted_invariant
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (order: t -> t -> bool)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn2: R.ref SZ.t)
  (pres: R.ref bool)
  (cont: bool)
: Tot vprop
= nlist_sorted_invariant0 p order n0 va0 a0 pa pn2 pres cont

#set-options "--ide_id_info_off"

let intro_nlist_sorted_invariant
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (order: t -> t -> bool)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn2: R.ref SZ.t)
  (pres: R.ref bool)
  (#n: nat)
  (#va: v (parse_nlist_kind n k) (nlist n t))
  (#va1: v k t)
  (#n2: SZ.t)
  (#va2: v (parse_nlist_kind (SZ.v n2) k) (nlist (SZ.v n2) t))
  (#a: byte_array)
  (#a2: byte_array)
  (#res: bool)
  (cont: bool)
: STGhost unit opened
  (
    R.pts_to pn2 full_perm n2 `star`
    nlist_iterator p n0 va0 a0 n va `star`
    R.pts_to pa full_perm a `star`
    aparse p a va1 `star`
    aparse (parse_nlist (SZ.v n2) p) a2 va2 `star`
    R.pts_to pres full_perm res
  )
  (fun _ ->
    nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres cont
  )
  (n == SZ.v n2 + 1 /\
    nlist_sorted_invariant_prop k t order n0 va0 n2 va va1 va2 res cont)
  (fun _ -> True)
= let w = {
    n2 = n2;
    a = a;
    va = va;
    va1 = va1;
    a2 = a2;
    va2 = va2;
    res = res;
  }
  in
  rewrite (nlist_iterator p n0 va0 a0 _ _) (nlist_iterator p n0 va0 a0 (SZ.v w.n2 + 1) w.va);
  rewrite (aparse _ a _) (aparse p w.a w.va1);
  rewrite (aparse _ a2 _) (aparse (parse_nlist (SZ.v w.n2) p) w.a2 w.va2);
  noop ();
  rewrite
    (nlist_sorted_invariant0 p order n0 va0 a0 pa pn2 pres cont)
    (nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres cont)

let elim_nlist_sorted_invariant
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (order: t -> t -> bool)
  (n0: nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn2: R.ref SZ.t)
  (pres: R.ref bool)
  (cont: bool)
: STGhost (nlist_sorted_invariant_t k t) opened
    (nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres cont)
    (fun w -> nlist_sorted_invariant_body p order n0 va0 a0 pa pn2 pres cont w)
    True
    (fun w -> nlist_sorted_invariant_prop k t order n0 va0 w.n2 w.va w.va1 w.va2 w.res cont)
= rewrite
    (nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres cont)
    (nlist_sorted_invariant0 p order n0 va0 a0 pa pn2 pres cont);
  let w = elim_exists () in
  elim_pure _;
  w

inline_for_extraction
let order_impl
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (order: Ghost.erased (t -> t -> bool))
: Tot Type
= 
  (#va1: v k t) ->
  (#va2: v k t) ->
  (a1: byte_array) ->
  (a2: byte_array) ->
  ST bool
    (aparse p a1 va1 `star` aparse p a2 va2)
    (fun _ -> aparse p a1 va1 `star` aparse p a2 va2)
    True
    (fun res -> res == Ghost.reveal order va1.contents va2.contents)

inline_for_extraction
let nlist_sorted_step
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (#p: parser k t)
  (j: jumper p)
  (#order: Ghost.erased (t -> t -> bool))
  (f_order: order_impl p order)
  (n0: Ghost.erased nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn2: R.ref SZ.t)
  (pres: R.ref bool)
  ()
: STT unit
    (nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres true)
    (fun _ -> exists_ (nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres))
= let w = elim_nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres true in
  let a = R.read pa in
  vpattern_rewrite (fun a -> aparse p a _) a;
  let a2 = hop_aparse_aparse j _ a w.a2 in
  R.write pa a2;
  let n2 = R.read pn2 in
  let n2' = n2 `SZ.sub` 1sz in
  R.write pn2 n2';
  let a2' = elim_nlist_cons p (SZ.v w.n2) (SZ.v n2') a2 in
  let _ = gen_elim () in
  let res = f_order a a2 in
  R.write pres res;
  nlist_iterator_next p a0 a w.va2;
  intro_nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres (res && (n2' `SZ.gt` 0sz));
  noop ()

inline_for_extraction
let nlist_sorted_test
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (order: Ghost.erased (t -> t -> bool))
  (n0: Ghost.erased nat)
  (va0: v (parse_nlist_kind n0 k) (nlist n0 t))
  (a0: byte_array)
  (pa: R.ref byte_array)
  (pn2: R.ref SZ.t)
  (pres: R.ref bool)
  ()
: STT bool
    (exists_ (nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres))
    (fun cont -> nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres cont)
= let _ = elim_exists () in
  let w = elim_nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres _ in
  let res = R.read pres in
  let n2 = R.read pn2 in
  [@@inline_let]
  let cont = res && (n2 `SZ.gt` 0sz) in
  intro_nlist_sorted_invariant p order n0 va0 a0 pa pn2 pres cont;
  return cont

inline_for_extraction
let intro_refinement
  (#t: Type)
  (p: (t ->  prop))
  (x: t)
: Pure (x: t { p x })
    (requires (p x))
    (ensures (fun _ -> True))
= x

#push-options "--z3rlimit 16 --split_queries always"

#restart-solver
inline_for_extraction
let nlist_sorted_nonempty
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (#p: parser k t)
  (j: jumper p)
  (#order: Ghost.erased (t -> t -> bool))
  (f_order: order_impl p order)
  (n0: SZ.t)
  (va0: v (parse_nlist_kind (SZ.v n0) k) (nlist (SZ.v n0) t))
  (a0: byte_array)
: ST bool
    (aparse (parse_nlist (SZ.v n0) p) a0 va0)
    (fun _ -> aparse (parse_nlist (SZ.v n0) p) a0 va0)
    (k.parser_kind_subkind == Some ParserStrong /\
      SZ.v n0 >= 2
    )
    (fun res -> res == List.Tot.sorted order va0.contents)
=
  let _ = nlist_iterator_begin p #(SZ.v n0) a0 in
  let n2 = n0 `SZ.sub` 1sz in
  let a2 = elim_nlist_cons p (SZ.v n0) (SZ.v n2) a0 in
  let _ = gen_elim () in
  noop ();
  let res : (res: bool { res == List.Tot.sorted order va0.contents }) =
    R.with_local a0 (fun pa ->
    R.with_local n2 (fun pn2 ->
    R.with_local true (fun pres ->
      intro_nlist_sorted_invariant p order (SZ.v n0) va0 a0 pa pn2 pres true;
      Steel.ST.Loops.while_loop
        (nlist_sorted_invariant p order (SZ.v n0) va0 a0 pa pn2 pres)
        (nlist_sorted_test p order (SZ.v n0) va0 a0 pa pn2 pres)
        (nlist_sorted_step j f_order (SZ.v n0) va0 a0 pa pn2 pres);
      let w = elim_nlist_sorted_invariant p order (SZ.v n0) va0 a0 pa pn2 pres false in
      noop ();
      let res = R.read pres in
      nlist_iterator_next p a0 w.a w.va2;
      nlist_iterator_end p a0 w.a2;
      return (intro_refinement (fun res -> res == List.Tot.sorted order va0.contents) res)
    )))
  in
  return res

#pop-options

inline_for_extraction
let nlist_sorted
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (#p: parser k t)
  (j: jumper p)
  (#order: Ghost.erased (t -> t -> bool))
  (f_order: order_impl p order)
  (n0: SZ.t)
  (va0: v (parse_nlist_kind (SZ.v n0) k) (nlist (SZ.v n0) t))
  (a0: byte_array)
: ST bool
    (aparse (parse_nlist (SZ.v n0) p) a0 va0)
    (fun _ -> aparse (parse_nlist (SZ.v n0) p) a0 va0)
    (k.parser_kind_subkind == Some ParserStrong)
    (fun res -> res == List.Tot.sorted order va0.contents)
= if n0 `SZ.lt` 2sz
  then begin
    noop ();
    return true
  end else begin
    nlist_sorted_nonempty j f_order n0 va0 a0
  end

module I16 = FStar.Int16

let nlist_lex_compare_invariant_prop
  (k: parser_kind)
  (t: Type)
  (compare: t -> t -> int)
  (na0: nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (nb0: nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (nan: nat)
  (va: v (parse_nlist_kind nan k) (nlist nan t))
  (na: SZ.t)
  (nbn: nat)
  (vb: v (parse_nlist_kind nbn k) (nlist nbn t))
  (nb: SZ.t)
  (res: I16.t)
  (a ga b gb: byte_array)
  (cont: bool)
: GTot prop
= nan == SZ.v na /\
  nbn == SZ.v nb /\
  cont == ((res = 0s) && SZ.v na > 0 && SZ.v nb > 0) /\
  lex_compare compare va0.contents vb0.contents == (if cont then lex_compare compare va.contents vb.contents else I16.v res) /\
  (cont == true ==> (a == ga /\ b == gb)) /\
  k.parser_kind_subkind == Some ParserStrong

[@@__reduce__]
let nlist_lex_compare_invariant_body
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (compare: t -> t -> int)
  (na0: nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (a0: byte_array)
  (nb0: nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (b0: byte_array)
  (pa: R.ref byte_array)
  (pb: R.ref byte_array)
  (pna: R.ref SZ.t)
  (pnb: R.ref SZ.t)
  (pres: R.ref I16.t)
  (nan: nat)
  (va: v (parse_nlist_kind nan k) (nlist nan t))
  (na: SZ.t)
  (nbn: nat)
  (vb: v (parse_nlist_kind nbn k) (nlist nbn t))
  (nb: SZ.t)
  (res: I16.t)
  (a ga b gb: byte_array)
  (cont: bool)
: Tot vprop
=   nlist_iterator p na0 va0 a0 nan va `star`
    nlist_iterator p nb0 vb0 b0 nbn vb `star`
    R.pts_to pa full_perm a `star` aparse (parse_nlist nan p) ga va `star` R.pts_to pna full_perm na `star`
    R.pts_to pb full_perm b `star` aparse (parse_nlist nbn p) gb vb `star` R.pts_to pnb full_perm nb `star`
    R.pts_to pres full_perm res

[@@erasable]
noeq
type nlist_lex_compare_invariant_t
  (k: parser_kind)
  (t: Type)
= {
  na: SZ.t;
  va: v (parse_nlist_kind (SZ.v na) k) (nlist (SZ.v na) t);
  nb: SZ.t;
  vb: v (parse_nlist_kind (SZ.v nb) k) (nlist (SZ.v nb) t);
  res: I16.t;
  a: byte_array;
  ga: byte_array;
  b: byte_array;
  gb: byte_array;
}

[@@__reduce__]
let nlist_lex_compare_invariant1
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (compare: t -> t -> int)
  (na0: nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (a0: byte_array)
  (nb0: nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (b0: byte_array)
  (pa: R.ref byte_array)
  (pb: R.ref byte_array)
  (pna: R.ref SZ.t)
  (pnb: R.ref SZ.t)
  (pres: R.ref I16.t)
  (cont: bool)
  (w: nlist_lex_compare_invariant_t k t)
: Tot vprop
= nlist_lex_compare_invariant_body p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres (SZ.v w.na) w.va w.na (SZ.v w.nb) w.vb w.nb w.res w.a w.ga w.b w.gb cont

let nlist_lex_compare_invariant_prop1
  (k: parser_kind)
  (t: Type)
  (compare: t -> t -> int)
  (na0: nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (nb0: nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (w: nlist_lex_compare_invariant_t k t)
  (cont: bool)
: GTot prop
= nlist_lex_compare_invariant_prop k t compare na0 va0 nb0 vb0 (SZ.v w.na) w.va w.na (SZ.v w.nb) w.vb w.nb w.res w.a w.ga w.b w.gb cont

[@@__reduce__]
let nlist_lex_compare_invariant0
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (compare: t -> t -> int)
  (na0: nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (a0: byte_array)
  (nb0: nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (b0: byte_array)
  (pa: R.ref byte_array)
  (pb: R.ref byte_array)
  (pna: R.ref SZ.t)
  (pnb: R.ref SZ.t)
  (pres: R.ref I16.t)
  (cont: bool)
: Tot vprop
= exists_ (fun w -> nlist_lex_compare_invariant1 p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres cont w `star` 
    pure (nlist_lex_compare_invariant_prop1 k t compare na0 va0 nb0 vb0 w cont)
  )

let nlist_lex_compare_invariant
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (compare: t -> t -> int)
  (na0: nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (a0: byte_array)
  (nb0: nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (b0: byte_array)
  (pa: R.ref byte_array)
  (pb: R.ref byte_array)
  (pna: R.ref SZ.t)
  (pnb: R.ref SZ.t)
  (pres: R.ref I16.t)
  (cont: bool)
: Tot vprop
= nlist_lex_compare_invariant0 p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres cont

let intro_nlist_lex_compare_invariant
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (compare: t -> t -> int)
  (na0: nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (a0: byte_array)
  (nb0: nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (b0: byte_array)
  (pa: R.ref byte_array)
  (pb: R.ref byte_array)
  (pna: R.ref SZ.t)
  (pnb: R.ref SZ.t)
  (pres: R.ref I16.t)
  (#nan: nat)
  (#va: v (parse_nlist_kind nan k) (nlist nan t))
  (#na: SZ.t)
  (#nbn: nat)
  (#vb: v (parse_nlist_kind nbn k) (nlist nbn t))
  (#nb: SZ.t)
  (#res: I16.t)
  (#a ga #b gb: byte_array)
  (cont: bool)
: STGhost unit opened
    (nlist_lex_compare_invariant_body p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres nan va na nbn vb nb res a ga b gb cont)
    (fun _ -> nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres cont)
    (nlist_lex_compare_invariant_prop k t compare na0 va0 nb0 vb0 nan va na nbn vb nb res a ga b gb cont)
    (fun _ -> True)
= let w : nlist_lex_compare_invariant_t k t = {
    na = na;
    va = va;
    nb = nb;
    vb = vb;
    res = res;
    a = a;
    ga = ga;
    b = b;
    gb = gb;
  }
  in
  noop ();
  rewrite
    (nlist_lex_compare_invariant_body p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres nan va na nbn vb nb res a ga b gb cont)
    (nlist_lex_compare_invariant1 p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres cont w)
  ;
  rewrite
    (nlist_lex_compare_invariant0 p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres cont)
    (nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres cont)

let elim_nlist_lex_compare_invariant
  (#opened: _)
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (compare: t -> t -> int)
  (na0: nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (a0: byte_array)
  (nb0: nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (b0: byte_array)
  (pa: R.ref byte_array)
  (pb: R.ref byte_array)
  (pna: R.ref SZ.t)
  (pnb: R.ref SZ.t)
  (pres: R.ref I16.t)
  (cont: bool)
: STGhost (nlist_lex_compare_invariant_t k t) opened
    (nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres cont)
    (fun w -> nlist_lex_compare_invariant1 p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres cont w)
    True
    (fun w -> nlist_lex_compare_invariant_prop1 k t compare na0 va0 nb0 vb0 w cont)
= let w = elim_exists () in
  let _ = gen_elim () in
  w

inline_for_extraction
let compare_impl
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (compare: Ghost.erased (t -> t -> int))
: Tot Type
= 
  (#va1: v k t) ->
  (#va2: v k t) ->
  (a1: byte_array) ->
  (a2: byte_array) ->
  ST I16.t
    (aparse p a1 va1 `star` aparse p a2 va2)
    (fun _ -> aparse p a1 va1 `star` aparse p a2 va2)
    True
    (fun res -> I16.v res == Ghost.reveal compare va1.contents va2.contents)

#push-options "--z3rlimit 16 --split_queries always --fuel 3 --ifuel 6 --query_stats"

#restart-solver
inline_for_extraction
let nlist_lex_compare_body
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (#p: parser k t)
  (j: jumper p)
  (compare: Ghost.erased (t -> t -> int))
  (f_compare: compare_impl p compare)
  (na0: Ghost.erased nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (a0: Ghost.erased byte_array)
  (nb0: Ghost.erased nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (b0: Ghost.erased byte_array)
  (pa: R.ref byte_array)
  (pb: R.ref byte_array)
  (pna: R.ref SZ.t)
  (pnb: R.ref SZ.t)
  (pres: R.ref I16.t)
  ()
: STT unit
   (nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres true)
   (fun _ -> exists_ (nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres))
= let w = elim_nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres true in
  let a = R.read pa in
  vpattern_rewrite #_ #_ #w.ga (fun a -> aparse _ a _) a;
  let na = R.read pna in
  let na' = na `SZ.sub` 1sz in
  let a' = elim_nlist_cons _ _ (SZ.v na') a in
  let _ = gen_elim () in
  let va' = vpattern_replace (aparse _ a') in
  let b = R.read pb in
  vpattern_rewrite #_ #_ #w.gb (fun a -> aparse _ a _) b;
  let nb = R.read pnb in
  let nb' = nb `SZ.sub` 1sz in
  let b' = elim_nlist_cons _ _ (SZ.v nb') b in
  let _ = gen_elim () in
  let vb' = vpattern_replace (aparse _ b') in
  let comp = f_compare a b in
  if comp <> 0s
  then begin
    R.write pres comp;
    intro_nlist_cons_with (SZ.v w.na) p _ a a' w.va;
    intro_nlist_cons_with (SZ.v w.nb) p _ b b' w.vb;
    intro_nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres a b false;
    return ()
  end else begin
    R.write pna na';
    R.write pnb nb';
    if na' = 0sz
    then begin
      r_write_if (nb' <> 0sz) pres (-1s);
      nlist_iterator_next p a0 a va';
      nlist_iterator_next p b0 b vb';
      intro_nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres a' b' false;
      return ()
    end else if nb' = 0sz
    then begin
      R.write pres 1s;
      nlist_iterator_next p a0 a va';
      nlist_iterator_next p b0 b vb';
      intro_nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres a' b' false;
      return ()
    end else begin
      let a' = hop_aparse_aparse j _ a a' in
      R.write pa a';
      let b' = hop_aparse_aparse j _ b b' in
      R.write pb b';
      nlist_iterator_next p a0 a va';
      nlist_iterator_next p b0 b vb';
      intro_nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres a' b' true;
      return ()
    end
  end

inline_for_extraction
let nlist_lex_compare_test
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (p: parser k t)
  (compare: Ghost.erased (t -> t -> int))
  (na0: Ghost.erased nat)
  (va0: v (parse_nlist_kind na0 k) (nlist na0 t))
  (a0: Ghost.erased byte_array)
  (nb0: Ghost.erased nat)
  (vb0: v (parse_nlist_kind nb0 k) (nlist nb0 t))
  (b0: Ghost.erased byte_array)
  (pa: R.ref byte_array)
  (pb: R.ref byte_array)
  (pna: R.ref SZ.t)
  (pnb: R.ref SZ.t)
  (pres: R.ref I16.t)
  ()
: STT bool
   (exists_ (nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres))
   (fun cont -> nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres cont)
= let gcont = elim_exists () in
  let w = elim_nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres gcont in
  let res = R.read pres in
  let na = R.read pna in
  let nb = R.read pnb in
  let cont = ((res = 0s) && (na `SZ.gt` 0sz) && (nb `SZ.gt` 0sz)) in
  noop ();
  intro_nlist_lex_compare_invariant p compare na0 va0 a0 nb0 vb0 b0 pa pb pna pnb pres w.ga w.gb cont;
  return cont

inline_for_extraction
let nlist_lex_compare_nonempty
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (#p: parser k t)
  (j: jumper p)
  (compare: Ghost.erased (t -> t -> int))
  (f_compare: compare_impl p compare)
  (na0: SZ.t)
  (#va0: v (parse_nlist_kind (SZ.v na0) k) (nlist (SZ.v na0) t))
  (a0: byte_array)
  (nb0: SZ.t)
  (#vb0: v (parse_nlist_kind (SZ.v nb0) k) (nlist (SZ.v nb0) t))
  (b0: byte_array)
: ST I16.t
    (aparse (parse_nlist (SZ.v na0) p) a0 va0 `star` aparse (parse_nlist (SZ.v nb0) p) b0 vb0)
    (fun _ -> aparse (parse_nlist (SZ.v na0) p) a0 va0 `star` aparse (parse_nlist (SZ.v nb0) p) b0 vb0)
    (SZ.v na0 > 0 /\ SZ.v nb0 > 0 /\
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> I16.v res == lex_compare compare va0.contents vb0.contents)
= let res : (res: I16.t { I16.v res == lex_compare compare va0.contents vb0.contents }) =
    let _ = nlist_iterator_begin p #(SZ.v na0) #va0 a0 in
    let _ = nlist_iterator_begin p #(SZ.v nb0) #vb0 b0 in
    R.with_local a0 (fun pa ->
    R.with_local b0 (fun pb ->
    R.with_local na0 (fun pna ->
    R.with_local nb0 (fun pnb ->
    R.with_local 0s (fun pres ->
      noop ();
      intro_nlist_lex_compare_invariant p compare (SZ.v na0) va0 a0 (SZ.v nb0) vb0 b0 pa pb pna pnb pres a0 b0 true;
      Steel.ST.Loops.while_loop
        (nlist_lex_compare_invariant p compare (SZ.v na0) va0 a0 (SZ.v nb0) vb0 b0 pa pb pna pnb pres)
        (nlist_lex_compare_test p compare (SZ.v na0) va0 a0 (SZ.v nb0) vb0 b0 pa pb pna pnb pres)
        (nlist_lex_compare_body j compare f_compare (SZ.v na0) va0 a0 (SZ.v nb0) vb0 b0 pa pb pna pnb pres);
      let w = elim_nlist_lex_compare_invariant p compare (SZ.v na0) va0 a0 (SZ.v nb0) vb0 b0 pa pb pna pnb pres false in
      let res = R.read pres in
      nlist_iterator_end p #(SZ.v na0) #va0 #(SZ.v w.na) #(w.va) a0 w.ga;
      nlist_iterator_end p #(SZ.v nb0) #vb0 #(SZ.v w.nb) #(w.vb) b0 w.gb;
      return (intro_refinement (fun res -> I16.v res == lex_compare compare va0.contents vb0.contents) res)
    )))))
  in
  return res

inline_for_extraction
let nlist_lex_compare
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (#p: parser k t)
  (j: jumper p)
  (compare: Ghost.erased (t -> t -> int))
  (f_compare: compare_impl p compare)
  (na0: SZ.t)
  (#va0: v (parse_nlist_kind (SZ.v na0) k) (nlist (SZ.v na0) t))
  (a0: byte_array)
  (nb0: SZ.t)
  (#vb0: v (parse_nlist_kind (SZ.v nb0) k) (nlist (SZ.v nb0) t))
  (b0: byte_array)
: ST I16.t
    (aparse (parse_nlist (SZ.v na0) p) a0 va0 `star` aparse (parse_nlist (SZ.v nb0) p) b0 vb0)
    (fun _ -> aparse (parse_nlist (SZ.v na0) p) a0 va0 `star` aparse (parse_nlist (SZ.v nb0) p) b0 vb0)
    (
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> I16.v res == lex_compare compare va0.contents vb0.contents)
= if na0 = 0sz
  then
    if nb0 = 0sz
    then return 0s
    else return (-1s)
  else if nb0 = 0sz
  then return 1s
  else return (nlist_lex_compare_nonempty j compare f_compare na0 a0 nb0 b0)

#pop-options

inline_for_extraction
let nlist_lex_order
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (#p: parser k t)
  (j: jumper p)
  (compare: Ghost.erased (t -> t -> int))
  (f_compare: compare_impl p compare)
  (na0: SZ.t)
  (#va0: v (parse_nlist_kind (SZ.v na0) k) (nlist (SZ.v na0) t))
  (a0: byte_array)
  (nb0: SZ.t)
  (#vb0: v (parse_nlist_kind (SZ.v nb0) k) (nlist (SZ.v nb0) t))
  (b0: byte_array)
: ST bool
    (aparse (parse_nlist (SZ.v na0) p) a0 va0 `star` aparse (parse_nlist (SZ.v nb0) p) b0 vb0)
    (fun _ -> aparse (parse_nlist (SZ.v na0) p) a0 va0 `star` aparse (parse_nlist (SZ.v nb0) p) b0 vb0)
    (
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> res == lex_order compare va0.contents vb0.contents)
= let comp = nlist_lex_compare j compare f_compare na0 a0 nb0 b0 in
  return (comp `I16.lt` 0s)

inline_for_extraction
let nlist_length_first_lex_order
  (#k: Ghost.erased parser_kind)
  (#t: Type0) // gen_elim universe issue
  (#p: parser k t)
  (j: jumper p)
  (compare: Ghost.erased (t -> t -> int))
  (f_compare: compare_impl p compare)
  (na0: SZ.t)
  (#va0: v (parse_nlist_kind (SZ.v na0) k) (nlist (SZ.v na0) t))
  (a0: byte_array)
  (nb0: SZ.t)
  (#vb0: v (parse_nlist_kind (SZ.v nb0) k) (nlist (SZ.v nb0) t))
  (b0: byte_array)
: ST bool
    (aparse (parse_nlist (SZ.v na0) p) a0 va0 `star` aparse (parse_nlist (SZ.v nb0) p) b0 vb0)
    (fun _ -> aparse (parse_nlist (SZ.v na0) p) a0 va0 `star` aparse (parse_nlist (SZ.v nb0) p) b0 vb0)
    (
      k.parser_kind_subkind == Some ParserStrong
    )
    (fun res -> res == length_first_lex_order compare va0.contents vb0.contents)
= if na0 = nb0
  then nlist_lex_order j compare f_compare na0 a0 nb0 b0
  else return (na0 `SZ.lt` nb0)
