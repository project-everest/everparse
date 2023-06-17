module LowParse.SteelST.VCList.Sorted
include LowParse.SteelST.VCList.Iterator
include LowParse.Spec.Sorted

module AP = LowParse.SteelST.ArrayPtr
module Swap = LowParse.SteelST.Swap
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

val intro_nlist_sorted_invariant
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

inline_for_extraction
let compare_impl_with
  (#kkey: Ghost.erased parser_kind)
  (#tkey: Type)
  (pkey: parser kkey tkey)
  (key_compare: Ghost.erased (tkey -> tkey -> int))
  (key: Ghost.erased tkey)
  (rkey: vprop)
: Tot Type
= (#va: v kkey tkey) ->
  (a: byte_array) ->
  (sz: SZ.t) ->
  ST I16.t
    (rkey `star` aparse pkey a va)
    (fun _ -> rkey `star` aparse pkey a va)
    (SZ.v sz == AP.length (array_of va))
    (fun res ->
      same_sign (I16.v res) (Ghost.reveal key_compare key va.contents)
    )

inline_for_extraction
let compare_impl
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (compare: Ghost.erased (t -> t -> int))
: Tot Type
= 
  (#va1: v k t) ->
  (a1: byte_array) ->
  (sz1: SZ.t) ->
  Pure (compare_impl_with p compare va1.contents (aparse p a1 va1))
    (SZ.v sz1 == AP.length (array_of va1))
    (fun _ -> True)

(* Inserting an element into a sorted list, when this element is immediately adjacent to the left of the list *)

[@@__reduce__]
let nlist_insert_post_true
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
: Tot vprop
= exists_ (fun (va: v (parse_nlist_kind (SZ.v nr + 1) k) (nlist (SZ.v nr + 1) t)) ->
    aparse (parse_nlist (SZ.v nr + 1) p) al va `star`
    pure (
      AP.merge_into (array_of vl) (array_of vr) (array_of va) /\
      insert compare vl.contents vr.contents == Some va.contents
    )
  )

[@@__reduce__]
let nlist_insert_post_false
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
: Tot vprop
= aparse p al vl `star`
  aparse (parse_nlist (SZ.v nr) p) ar vr `star`
  pure (insert compare vl.contents vr.contents == None)

let nlist_insert_post
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (res: bool)
: Tot vprop
= if res
  then nlist_insert_post_true p compare al vl ar nr vr
  else nlist_insert_post_false p compare al vl ar nr vr

let nlist_insert_post_some
  (#opened: _)
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (res: bool)
: STGhost (v (parse_nlist_kind (SZ.v nr + 1) k) (nlist (SZ.v nr + 1) t)) opened
    (nlist_insert_post p compare al vl ar nr vr res)
    (fun va ->
      aparse (parse_nlist (SZ.v nr + 1) p) al va
    )
    (
      Some? (insert compare vl.contents vr.contents)
    )
    (fun va ->
      AP.merge_into (array_of vl) (array_of vr) (array_of va) /\
      insert compare vl.contents vr.contents == Some va.contents
    )
= if res
  then begin
    rewrite
      (nlist_insert_post p compare al vl ar nr vr _)
      (nlist_insert_post_true p compare al vl ar nr vr);
    let _ = gen_elim () in
    let va = vpattern_replace (aparse (parse_nlist (SZ.v nr + 1) p) al) in
    va
  end else begin
    rewrite
      (nlist_insert_post p compare al vl ar nr vr _)
      (nlist_insert_post_false p compare al vl ar nr vr);
    let _ = gen_elim () in
    let va : v (parse_nlist_kind (SZ.v nr + 1) k) (nlist (SZ.v nr + 1) t) = false_elim () in
    rewrite // by contradiction
      (nlist_insert_post_false p compare al vl ar nr vr)
      (aparse (parse_nlist (SZ.v nr + 1) p) al va);
    va
  end

[@@CMacro]
let nlist_insert_in_progress : byte = 0uy

[@@CMacro]
let nlist_insert_success : byte = 1uy

[@@CMacro]
let nlist_insert_failure : byte = 2uy

[@@erasable]
noeq
type nlist_insert_invariant_body_in_progress_t
  (k: parser_kind)
  (t: Type)
= {
    nrl: nat;
    szrl: SZ.t;
    nrr: SZ.t;
    vrl: v (parse_nlist_kind nrl k) (nlist nrl t);
    arr: byte_array;
    vrr: v (parse_nlist_kind (SZ.v nrr) k) (nlist (SZ.v nrr) t);
  }

[@@__reduce__]
let nlist_insert_invariant_body_in_progress_body
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
  (nrl: nat)
  (szrl: SZ.t)
  (nrr: SZ.t)
  (vrl: v (parse_nlist_kind nrl k) (nlist nrl t))
  (arr: byte_array)
  (vrr: v (parse_nlist_kind (SZ.v nrr) k) (nlist (SZ.v nrr) t))
: Tot vprop
= aparse p al vl `star`
  aparse (parse_nlist nrl p) ar vrl `star`
  R.pts_to pszrl full_perm szrl `star`
  R.pts_to pnrr full_perm nrr `star`
  R.pts_to parr full_perm arr `star`
  aparse (parse_nlist (SZ.v nrr) p) arr vrr

let nlist_insert_invariant_body_in_progress_prop
  (k: Ghost.erased parser_kind)
  (#t: Type)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (vl: v k t)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (szrl: SZ.t)
  (nrl: nat)
  (nrr: SZ.t)
  (vrl: v (parse_nlist_kind nrl k) (nlist nrl t))
  (vrr: v (parse_nlist_kind (SZ.v nrr) k) (nlist (SZ.v nrr) t))
: Tot prop
=
  SZ.v szrl == AP.length (array_of vrl) /\
  nrl + SZ.v nrr == SZ.v nr /\
  AP.merge_into (array_of vrl) (array_of vrr) (array_of vr) /\
  (vr.contents <: list t) == List.Tot.append vrl.contents vrr.contents /\
  begin match insert compare vl.contents vr.contents, insert compare vl.contents vrr.contents with
  | None, None -> True
  | Some l, Some lr -> l == List.Tot.append vrl.contents lr
  | _ -> False
  end

[@@__reduce__]
let nlist_insert_invariant_body_in_progress0
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
: Tot vprop
= exists_ (fun w ->
    nlist_insert_invariant_body_in_progress_body p al vl ar pszrl pnrr parr w.nrl w.szrl w.nrr w.vrl w.arr w.vrr `star`
    pure (nlist_insert_invariant_body_in_progress_prop k compare vl nr vr w.szrl w.nrl w.nrr w.vrl w.vrr)
  )

let nlist_insert_invariant_body_in_progress
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
: Tot vprop
= nlist_insert_invariant_body_in_progress0 p compare al vl ar nr vr pszrl pnrr parr

let intro_nlist_insert_invariant_body_in_progress
  (#opened: _)
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
  (nrl: nat)
  (szrl: SZ.t)
  (nrr: SZ.t)
  (vrl: v (parse_nlist_kind nrl k) (nlist nrl t))
  (arr: byte_array)
  (vrr: v (parse_nlist_kind (SZ.v nrr) k) (nlist (SZ.v nrr) t))
: STGhost unit opened
    (nlist_insert_invariant_body_in_progress_body p al vl ar pszrl pnrr parr nrl szrl nrr vrl arr vrr)
    (fun _ -> nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr)
    (nlist_insert_invariant_body_in_progress_prop k compare vl nr vr szrl nrl nrr vrl vrr)
    (fun _ -> True)
= let w = {
    nrl = nrl;
    szrl = szrl;
    nrr = nrr;
    vrl = vrl;
    arr = arr;
    vrr = vrr;
  }
  in
  rewrite
    (nlist_insert_invariant_body_in_progress_body p al vl ar pszrl pnrr parr nrl szrl nrr vrl arr vrr)
    (nlist_insert_invariant_body_in_progress_body p al vl ar pszrl pnrr parr w.nrl w.szrl w.nrr w.vrl w.arr w.vrr);
  rewrite
    (nlist_insert_invariant_body_in_progress0 p compare al vl ar nr vr pszrl pnrr parr)
    (nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr)

let elim_nlist_insert_invariant_body_in_progress
  (#opened: _)
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
: STGhost (Ghost.erased (nlist_insert_invariant_body_in_progress_t k t)) opened
    (nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr)
    (fun w -> nlist_insert_invariant_body_in_progress_body p al vl ar pszrl pnrr parr w.nrl w.szrl w.nrr w.vrl w.arr w.vrr)
    True
    (fun w -> nlist_insert_invariant_body_in_progress_prop k compare vl nr vr w.szrl w.nrl w.nrr w.vrl w.vrr)
= let w = elim_exists () in
  let _ = gen_elim () in
  w

[@@__reduce__]
let nlist_insert_invariant_body_end
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
  (state: byte)
: Tot vprop
= exists_ (R.pts_to pszrl full_perm) `star`
  exists_ (R.pts_to pnrr full_perm) `star`
  exists_ (R.pts_to parr full_perm) `star`
  nlist_insert_post p compare al vl ar nr vr (state = nlist_insert_success)

let nlist_insert_invariant_body
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
  (state: byte)
: Tot vprop
= if state = nlist_insert_in_progress
  then nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr
  else nlist_insert_invariant_body_end p compare al vl ar nr vr pszrl pnrr parr state

[@@__reduce__]
let nlist_insert_invariant0
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
  (pstate: R.ref byte)
  (b: bool)
: Tot vprop
= exists_ (fun state -> 
    R.pts_to pstate full_perm state `star`
    nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr state `star`
    pure (b == (state = nlist_insert_in_progress))
  )

let nlist_insert_invariant
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
  (pstate: R.ref byte)
  (b: bool)
: Tot vprop
= nlist_insert_invariant0 p compare al vl ar nr vr pszrl pnrr parr pstate b

let intro_nlist_insert_invariant
  (#opened: _)
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
  (pstate: R.ref byte)
  (b: bool)
  (state: byte)
: STGhost unit opened
    (R.pts_to pstate full_perm state `star`
      nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr state)
    (fun _ -> nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate b)
    (b == (state = nlist_insert_in_progress))
    (fun _ -> True)
= noop ();
  rewrite
    (nlist_insert_invariant0 p compare al vl ar nr vr pszrl pnrr parr pstate b)
    (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate b)

let elim_nlist_insert_invariant
  (#opened: _)
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (p: parser k t)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (al: byte_array)
  (vl: v k t)
  (ar: byte_array)
  (nr: SZ.t)
  (vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
  (pstate: R.ref byte)
  (b: bool)
: STGhost (Ghost.erased byte) opened
    (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate b)
    (fun state -> R.pts_to pstate full_perm state `star`
      nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr state)
    True
    (fun state -> b == (Ghost.reveal state = nlist_insert_in_progress))
= rewrite
    (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate b)
    (nlist_insert_invariant0 p compare al vl ar nr vr pszrl pnrr parr pstate b);
  let _ = gen_elim () in
  _

inline_for_extraction
let size_add_le
  (s1 s2: SZ.t)
  (bound: Ghost.erased SZ.t)
  (sq: squash (SZ.v s1 + SZ.v s2 <= SZ.v bound))
: Tot SZ.t
= SZ.add s1 s2

#push-options "--z3rlimit 64"

#restart-solver
inline_for_extraction
let nlist_insert_with_size_body
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (comp: compare_impl p (Ghost.reveal compare))
  (#vl: v k t)
  (szl: SZ.t)
  (al: byte_array)
  (nr: SZ.t)
  (#vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (ar: byte_array)
  (sq: squash (
    k.parser_kind_subkind == Some ParserStrong /\
    AP.adjacent (array_of vl) (array_of vr) /\
    AP.array_perm (array_of vl) == full_perm /\
    SZ.v szl == AP.length (array_of vl)
  ))
  (pszrl: R.ref SZ.t)
  (pnrr: R.ref SZ.t)
  (parr: R.ref byte_array)
  (pstate: R.ref byte)
  ()
: STT unit
    (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate true)
    (fun _ -> exists_ (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate))
=
  let _ = elim_nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate true in
  rewrite
    (nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr _)
    (nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr);
  let w = elim_nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr in
  let nrr = R.read pnrr in
  let szrl = R.read pszrl in
  if nrr = 0sz
  then begin
    List.Tot.append_l_nil w.vrl.contents;
    let _ = elim_nlist_nil (SZ.v w.nrr) p w.arr in
    let _ = aparse_join_zero_r _ ar w.arr in
    rewrite (aparse _ ar _) (aparse (parse_nlist (SZ.v nr) p) ar vr);
    let ar' = Swap.swap_parsed_with_sizes al szl ar szrl in
    let _ = gen_elim () in
    let _ = intro_nlist_one p ar' 1 in
    let _ = intro_nlist_sum (SZ.v nr + 1) p _ al _ ar' in
    R.write pstate nlist_insert_success;
    rewrite
      (nlist_insert_post_true p compare al vl ar nr vr)
      (nlist_insert_post p compare al vl ar nr vr (nlist_insert_success = nlist_insert_success));
    rewrite
      (nlist_insert_invariant_body_end p compare al vl ar nr vr pszrl pnrr parr nlist_insert_success)
      (nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr nlist_insert_success);
    noop ();
    intro_nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate false _;
    return ()
  end else begin
    [@@inline_let]
    let nrr' = nrr `SZ.sub` 1sz in
    let arr = R.read parr in
    vpattern_rewrite #_ #_ #w.arr (fun arr -> aparse _ arr _) arr;
    let garr' = elim_nlist_cons p (SZ.v w.nrr) (SZ.v nrr') arr in
    let _ = gen_elim () in
    let szrr_hd = get_parsed_size j arr in
    let c = comp al szl arr szrr_hd in
    if c `I16.lt` 0s
    then begin
      let _ = intro_nlist_cons (SZ.v w.nrr) p _ arr garr' in
      let ar' = Swap.swap_parsed_with_sizes al szl ar szrl in
      let _ = gen_elim () in
      let _ = intro_nlist_cons (SZ.v w.nrr + 1) p _ ar' arr in
      let _ = intro_nlist_sum (SZ.v nr + 1) p _ al _ ar' in
      R.write pstate nlist_insert_success;
      rewrite
        (nlist_insert_post_true p compare al vl ar nr vr)
        (nlist_insert_post p compare al vl ar nr vr (nlist_insert_success = nlist_insert_success));
      rewrite
        (nlist_insert_invariant_body_end p compare al vl ar nr vr pszrl pnrr parr nlist_insert_success)
        (nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr nlist_insert_success);
      noop ();
      intro_nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate false _;
      return ()
    end else if c = 0s
    then begin
      let _ = intro_nlist_cons (SZ.v w.nrr) p _ arr garr' in
      let _ = intro_nlist_sum (SZ.v nr) p _ ar _ arr in
      vpattern_rewrite (aparse _ ar) vr;
      R.write pstate nlist_insert_failure;
      rewrite
        (nlist_insert_post_false p compare al vl ar nr vr)
        (nlist_insert_post p compare al vl ar nr vr (nlist_insert_failure = nlist_insert_success));
      rewrite
        (nlist_insert_invariant_body_end p compare al vl ar nr vr pszrl pnrr parr nlist_insert_failure)
        (nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr nlist_insert_failure);
      noop ();
      intro_nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate false _;
      return ()
    end else begin
      R.write pnrr nrr';
      let szrl = R.read pszrl in
      let arr' = hop_aparse_aparse_with_size _ _ arr szrr_hd garr' in
      R.write parr arr';
      let vrr_as_list = intro_nlist_one p arr 1 in
      let nrl' : Ghost.erased nat = Ghost.hide (w.nrl + 1) in
      let vrl' = intro_nlist_sum nrl' p _ ar _ arr in
      let sq_sz : squash (SZ.v szrl + SZ.v szrr_hd <= SZ.v (AP.len (array_of vrl'))) =
        assert (SZ.v szrl + SZ.v szrr_hd == SZ.v (AP.len (array_of vrl')))
      in
      noop ();
      [@@inline_let]
      let szrl' = size_add_le szrl szrr_hd (AP.len (array_of vrl')) sq_sz in
      R.write pszrl szrl';
      let vrr' : v (parse_nlist_kind (SZ.v nrr') k) (nlist (SZ.v nrr') t) = vpattern_replace (aparse (parse_nlist (SZ.v nrr') p) arr') in
      [@@inline_let]
      let prf
        ()
      : Lemma
        (match insert compare vl.contents vr.contents, insert compare vl.contents vrr'.contents with
        | None, None -> True
        | Some l, Some l' -> l == List.Tot.append vrl'.contents l'
        | _ -> False
        )
      = match insert compare vl.contents vrr'.contents with
        | None -> ()
        | Some l' -> List.Tot.append_assoc w.vrl.contents vrr_as_list.contents l'
      in
      prf ();
      List.Tot.append_assoc w.vrl.contents vrr_as_list.contents vrr'.contents;
      noop ();
      intro_nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr nrl' szrl' nrr' vrl' arr' vrr';
      rewrite
        (nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr)
        (nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr nlist_insert_in_progress);
      noop ();
      intro_nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate true nlist_insert_in_progress;
      return ()
    end
  end

#pop-options

inline_for_extraction
let nlist_insert_with_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (compare_impl: compare_impl p (Ghost.reveal compare))
  (#vl: v k t)
  (szl: SZ.t)
  (al: byte_array)
  (nr: SZ.t)
  (#vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (ar: byte_array)
: ST bool
    (aparse p al vl `star`
      aparse (parse_nlist (SZ.v nr) p) ar vr
    )
    (fun res -> nlist_insert_post p compare al vl ar nr vr res)
    (
      k.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of vl) (array_of vr) /\
      AP.array_perm (array_of vl) == full_perm /\
      SZ.v szl == AP.length (array_of vl)
    )
    (fun _ -> True)
= aparse_split_zero_l _ ar;
  let _ = gen_elim () in
  let vrr = vpattern_replace (aparse _ ar) in
  let vrl = intro_nlist_nil 0 p ar in
  R.with_local nlist_insert_in_progress (fun pstate ->
  R.with_local nr (fun pnrr ->
  R.with_local ar (fun parr ->
  R.with_local 0sz (fun pszrl ->
    intro_nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr 0 _ _ _ _ _;
    rewrite
      (nlist_insert_invariant_body_in_progress p compare al vl ar nr vr pszrl pnrr parr)
      (nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr nlist_insert_in_progress);
    rewrite
      (nlist_insert_invariant0 p compare al vl ar nr vr pszrl pnrr parr pstate true) 
      (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate true);
    Steel.ST.Loops.while_loop
      (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate)
      (fun _ ->
        let gb = elim_exists () in
        rewrite
          (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate _) 
          (nlist_insert_invariant0 p compare al vl ar nr vr pszrl pnrr parr pstate gb);
        let _ = gen_elim () in
        let state = R.read pstate in
        [@@inline_let]
        let res = state = nlist_insert_in_progress in
        noop ();
        rewrite
          (nlist_insert_invariant0 p compare al vl ar nr vr pszrl pnrr parr pstate res)
          (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate res);
        return res
      )
      (nlist_insert_with_size_body j compare compare_impl szl al nr ar () pszrl pnrr parr pstate);
    rewrite
      (nlist_insert_invariant p compare al vl ar nr vr pszrl pnrr parr pstate false) 
      (nlist_insert_invariant0 p compare al vl ar nr vr pszrl pnrr parr pstate false);
    let _ = gen_elim () in
    let state = R.read pstate in
    [@@inline_let]
    let res = state = nlist_insert_success in
    rewrite
      (nlist_insert_invariant_body p compare al vl ar nr vr pszrl pnrr parr _)
      (nlist_insert_invariant_body_end p compare al vl ar nr vr pszrl pnrr parr state);
    vpattern_rewrite (nlist_insert_post p compare al vl ar nr vr) res;
    noop ();
    return res
  ))))

inline_for_extraction
let nlist_insert
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (compare_impl: compare_impl p (Ghost.reveal compare))
  (#vl: v k t)
  (al: byte_array)
  (nr: SZ.t)
  (#vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (ar: byte_array)
: ST bool
    (aparse p al vl `star`
      aparse (parse_nlist (SZ.v nr) p) ar vr
    )
    (fun res -> nlist_insert_post p compare al vl ar nr vr res)
    (
      k.parser_kind_subkind == Some ParserStrong /\
      AP.adjacent (array_of vl) (array_of vr) /\
      AP.array_perm (array_of vl) == full_perm
    )
    (fun _ -> True)
= let szl = get_parsed_size j al in
  nlist_insert_with_size j compare compare_impl szl al nr ar

inline_for_extraction
let nlist_insert_some_with_size
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (compare_impl: compare_impl p (Ghost.reveal compare))
  (#vl: v k t)
  (szl: SZ.t)
  (al: byte_array)
  (nr: SZ.t)
  (#vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (ar: byte_array)
: ST (v (parse_nlist_kind (SZ.v nr + 1) k) (nlist (SZ.v nr + 1) t))
    (aparse p al vl `star`
      aparse (parse_nlist (SZ.v nr) p) ar vr
    )
    (fun va ->
      aparse (parse_nlist (SZ.v nr + 1) p) al va
    )
    (
      AP.adjacent (array_of vl) (array_of vr) /\
      k.parser_kind_subkind == Some ParserStrong /\
      AP.array_perm (array_of vl) == full_perm /\
      SZ.v szl == AP.length (array_of vl) /\
      Some? (insert compare vl.contents vr.contents)
    )
    (fun va ->
      AP.merge_into (array_of vl) (array_of vr) (array_of va) /\
      insert compare vl.contents vr.contents == Some va.contents
    )
= let _ = nlist_insert_with_size j compare compare_impl szl al nr ar in
  nlist_insert_post_some _ _ _ _ _ _ _ _

inline_for_extraction
let nlist_insert_some
  (#k: Ghost.erased parser_kind)
  (#t: Type)
  (#p: parser k t)
  (j: jumper p)
  (#order: Ghost.erased (t -> t -> bool))
  (compare: Ghost.erased (weak_compare_for order))
  (compare_impl: compare_impl p (Ghost.reveal compare))
  (#vl: v k t)
  (al: byte_array)
  (nr: SZ.t)
  (#vr: v (parse_nlist_kind (SZ.v nr) k) (nlist (SZ.v nr) t))
  (ar: byte_array)
: ST (v (parse_nlist_kind (SZ.v nr + 1) k) (nlist (SZ.v nr + 1) t))
    (aparse p al vl `star`
      aparse (parse_nlist (SZ.v nr) p) ar vr
    )
    (fun va ->
      aparse (parse_nlist (SZ.v nr + 1) p) al va
    )
    (
      AP.adjacent (array_of vl) (array_of vr) /\
      k.parser_kind_subkind == Some ParserStrong /\
      AP.array_perm (array_of vl) == full_perm /\
      Some? (insert compare vl.contents vr.contents)
    )
    (fun va ->
      AP.merge_into (array_of vl) (array_of vr) (array_of va) /\
      insert compare vl.contents vr.contents == Some va.contents
    )
= let szl = get_parsed_size j al in
  nlist_insert_some_with_size j compare compare_impl szl al nr ar

(* Lexicographic ordering *)

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
  same_sign (lex_compare compare va0.contents vb0.contents) (if cont then lex_compare compare va.contents vb.contents else I16.v res) /\
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
  let a_sz = get_parsed_size j a in
  let va' = vpattern_replace (aparse _ a') in
  let b = R.read pb in
  vpattern_rewrite #_ #_ #w.gb (fun a -> aparse _ a _) b;
  let nb = R.read pnb in
  let nb' = nb `SZ.sub` 1sz in
  let b' = elim_nlist_cons _ _ (SZ.v nb') b in
  let _ = gen_elim () in
  let b_sz = get_parsed_size j b in
  let vb' = vpattern_replace (aparse _ b') in
  let comp = f_compare a a_sz b b_sz in
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
      let a' = hop_aparse_aparse_with_size _ _ a a_sz a' in
      R.write pa a';
      let b' = hop_aparse_aparse_with_size _ _ b b_sz b' in
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
    (fun res -> I16.v res `same_sign` lex_compare compare va0.contents vb0.contents)
= let res : (res: I16.t { I16.v res `same_sign` lex_compare compare va0.contents vb0.contents }) =
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
      return (intro_refinement (fun res -> I16.v res `same_sign` lex_compare compare va0.contents vb0.contents) res)
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
    (fun res -> I16.v res `same_sign` lex_compare compare va0.contents vb0.contents)
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
