module LowParse.SteelST.VCList.Sorted
include LowParse.SteelST.VCList.Iterator

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
  let a = nlist_iterator_begin p #(SZ.v n0) a0 in
  let _ = gen_elim () in
  let n2 = n0 `SZ.sub` 1sz in
  let a2 = elim_nlist_cons p (SZ.v n0) (SZ.v n2) a in
  let _ = gen_elim () in
  noop ();
  let res : (res: bool { res == List.Tot.sorted order va0.contents }) =
    R.with_local a (fun pa ->
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
