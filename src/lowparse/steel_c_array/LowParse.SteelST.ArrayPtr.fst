module LowParse.SteelST.ArrayPtr
module STC = Steel.ST.C.Types

let t elt = STC.array_ptr (STC.scalar elt)

[@@erasable]
noeq
type array elt = {
  array_ptr: STC.array (STC.scalar elt);
  array_perm: Steel.FractionalPermission.perm;
//  array_base_len: (len: SZ.t { SZ.v len == SA.base_len (STC.base (STC.array_ptr_of array_ptr)) });
}

let len x = SZ.uint_to_t (STC.array_length x.array_ptr)

let array_perm x = x.array_perm

[@@erasable]
noeq
type v t = {
  v_array: array t;
  v_contents: Seq.lseq t (length v_array);
}

let array_of x = x.v_array
let contents_of x = x.v_contents

let array_contents_inj _ _ = ()

let mk_full_scalar_seq_index (#t: Type) (s: Seq.seq t) (i: nat { i < Seq.length s }) : GTot (STC.scalar_t t) =
  STC.mk_scalar (Seq.index s i)

let mk_full_scalar_seq (#t: Type) (s: Seq.seq t) : GTot (Seq.seq (STC.scalar_t t)) =
  Seq.init_ghost (Seq.length s) (mk_full_scalar_seq_index s)

let mk_scalar_seq (#t: Type) (p: perm) (s: Seq.seq t) : GTot (Seq.seq (STC.scalar_t t)) =
  STC.mk_fraction_seq (STC.scalar t) (mk_full_scalar_seq s) p

[@__reduce__]
let arrayptr1 (#elt: _) (v: v elt) (s: Ghost.erased (Seq.seq (STC.scalar_t elt))) : Tot vprop =
    STC.array_pts_to v.v_array.array_ptr s

[@__reduce__]
let arrayptr0 (#elt: _) (r: t elt) (v: v elt) : Tot vprop =
  exists_ (fun s ->
    arrayptr1 v s `star` pure (
    Ghost.reveal s `Seq.equal` mk_scalar_seq v.v_array.array_perm v.v_contents /\
    STC.array_ptr_of v.v_array.array_ptr == r /\
    (Seq.length v.v_contents > 0 ==> v.v_array.array_perm `lesser_equal_perm` full_perm)
  ))

let arrayptr r v = arrayptr0 r v
    
let adjacent x1 x2 =
  x1.array_perm == x2.array_perm /\
  STC.array_ptr_of x2.array_ptr == STC.array_ref_shift (STC.array_ptr_of x1.array_ptr) (len x1)

let merge x1 x2 = {
  array_ptr = (| STC.array_ptr_of x1.array_ptr, Ghost.hide (len x1 `SZ.add` len x2) |);
  array_perm = x1.array_perm;
//  array_base_len = x1.array_base_len;
}

let merge_assoc x1 x2 x3 =
  STC.array_ref_shift_assoc (STC.array_ptr_of x1.array_ptr) (len x1) (len x2)

let join #_ #a #vl #vr al ar =
  rewrite (arrayptr al vl) (arrayptr0 al vl);
  rewrite (arrayptr ar vr) (arrayptr0 ar vr);
  let _ = gen_elim () in
  let res = {
    v_array = merge (array_of vl) (array_of vr);
    v_contents = Seq.append vl.v_contents vr.v_contents;
  }
  in
  STC.array_join res.v_array.array_ptr vl.v_array.array_ptr vr.v_array.array_ptr (len (array_of vl));
  rewrite (arrayptr0 al res) (arrayptr al res);
  res

unfold
let gsplit_post
  (#a:Type) (value: v a) (x: t a) (i:SZ.t)
  (res: t a)
  (vl vr: v a)
: GTot prop
=
            SZ.v i <= length (array_of value) /\
            merge_into (array_of vl) (array_of vr) (array_of value) /\
            contents_of' vl `Seq.equal` seq_slice (contents_of' value) 0 (SZ.v i) /\
            length (array_of vl) == SZ.v i /\
            length (array_of vr) == length (array_of value) - SZ.v i /\
            contents_of' vr `Seq.equal` seq_slice (contents_of' value) (SZ.v i) (length (array_of value)) /\
            contents_of' value `Seq.equal` (contents_of' vl `Seq.append` contents_of' vr) /\
            (SZ.v i == 0 ==> Ghost.reveal res == x)

let gsplit #_ #_ #v x i =
  rewrite (arrayptr x v) (arrayptr0 x v);
  let _ = gen_elim () in
  let _ = STC.ghost_array_split _ i in
  let vl_array = {
    array_ptr = STC.array_split_l v.v_array.array_ptr i;
    array_perm = v.v_array.array_perm;
//    array_base_len = v.v_array.array_base_len;
  }
  in
  let vl = {
    v_array = vl_array;
    v_contents = Seq.slice v.v_contents 0 (SZ.v i);
  }
  in
  let vr_array = {
    array_ptr = STC.array_split_r v.v_array.array_ptr i;
    array_perm = v.v_array.array_perm;
//    array_base_len = v.v_array.array_base_len;
  }
  in
  let vr = {
    v_array = vr_array;
    v_contents = Seq.slice v.v_contents (SZ.v i) (Seq.length v.v_contents);
  }
  in
  let res = Ghost.hide (STC.array_ptr_of vr_array.array_ptr) in
  STC.array_ref_shift_zero x;
  let s = vpattern_replace (STC.array_pts_to (STC.array_split_l _ _)) in
  rewrite (STC.array_pts_to (STC.array_split_l _ _) _) (arrayptr1 vl s);
  rewrite (arrayptr0 x vl) (arrayptr x vl);
  let s = vpattern_replace (STC.array_pts_to _) in
  rewrite (STC.array_pts_to _ _) (arrayptr1 vr s);
  rewrite (arrayptr0 res vr) (arrayptr res vr);
  assert (gsplit_post v x i res vl vr);
  noop ();
  res

inline_for_extraction [@@noextract_to "krml"]
let stc_array_ref_split
  (#t: Type)
  (#td: STC.typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (al: STC.array_ref td)
  (len: STC.array_len_t al)
  (aa aal aar: Ghost.erased (STC.array td))
  (i: SZ.t)
: ST (_: STC.array_ref td { SZ.v i <= SZ.v len /\ Seq.length s == SZ.v len})
    (STC.array_pts_to aa s)
    (fun _ -> STC.array_pts_to aal (Seq.slice s 0 (SZ.v i)) `star`
      STC.array_pts_to aar (Seq.slice s (SZ.v i) (Seq.length s)))
    (SZ.v i <= SZ.v len /\
      Ghost.reveal aa == (| al, len |) /\
      Ghost.reveal aal == STC.array_split_l aa i /\
      Ghost.reveal aar == STC.array_split_r aa i
    )
    (fun ar ->
      Ghost.reveal aa == (| al, len |) /\
      ar == STC.array_ptr_of (STC.array_split_r aa i)
    )
= rewrite (STC.array_pts_to aa s) (STC.array_pts_to (| al, len |) s);
  let res = STC.array_ref_split al len i in
  let _ = gen_elim () in
  vpattern_rewrite (fun a -> STC.array_pts_to a _ `star` STC.array_pts_to (STC.array_split_r _ _) _) aal;
  vpattern_rewrite (fun a -> STC.array_pts_to aal _ `star` STC.array_pts_to a _) aar;
  vpattern_rewrite (STC.array_pts_to aal) _;
  vpattern_rewrite (STC.array_pts_to aar) _;
  return res

let split' #elt #vl #vr x i x' =
  rewrite (arrayptr x' vr) (arrayptr0 x' vr);
  let _ = gen_elim () in
  rewrite (arrayptr0 x' vr) (arrayptr x' vr);
  let vm = join x x' in
  rewrite (arrayptr x vm) (arrayptr0 x vm);
  let _ = gen_elim () in
  let res : t elt = stc_array_ref_split x (len vm.v_array) _ vl.v_array.array_ptr vr.v_array.array_ptr i in
  noop ();
  rewrite (arrayptr0 x vl) (arrayptr x vl);
  noop ();
  rewrite (arrayptr0 res vr) (arrayptr res vr);
  return res

let index #t #v r i =
  rewrite (arrayptr r v) (arrayptr0 r v);
  let _ = gen_elim () in
  [@@inline_let]
  let a : STC.array (STC.scalar t) = (| r, Ghost.hide (len v.v_array) |) in
  let s = vpattern_replace (STC.array_pts_to _) in
  vpattern_rewrite (fun a -> STC.array_pts_to a _) a;
  let p = STC.array_cell a i in
  let res = STC.read p in
  let _ = STC.unarray_cell a i p in
  drop (STC.has_array_cell _ _ _);
  let s' : Ghost.erased _ = vpattern_replace (STC.array_pts_to a) in
  assert (s' `Seq.equal` Ghost.reveal s);
  noop ();
  rewrite (STC.array_pts_to a s') (arrayptr1 v s);
  rewrite (arrayptr0 r v) (arrayptr r v);
  return res

let upd #elt #v r i x =
  rewrite (arrayptr r v) (arrayptr0 r v);
  let _ = gen_elim () in
  [@@inline_let]
  let a : STC.array (STC.scalar elt) = (| r, Ghost.hide (len v.v_array) |) in
  vpattern_rewrite (fun a -> STC.array_pts_to a _) a;
  let p = STC.array_cell a i in
  STC.write p x;
  let _ = STC.unarray_cell a i p in
  drop (STC.has_array_cell _ _ _);
  let s' = vpattern_replace (STC.array_pts_to _) in
  let res = {
    v_array = v.v_array;
    v_contents = Seq.upd v.v_contents (SZ.v i) x;
  }
  in
  rewrite (STC.array_pts_to _ _) (arrayptr1 res s');
  rewrite (arrayptr0 r res) (arrayptr r res);
  return res

let set_array_perm
  (#t: Type)
  (a: array t)
  (p: perm)
: Ghost (array t)
    (requires True)
    (ensures (fun y -> len y == len a /\ array_perm y == p))
= {
  a with array_perm = p
}

let set_array_perm_idem
  (#t: Type)
  (a: array t)
  (p1 p2: perm)
: Lemma
  (set_array_perm (set_array_perm a p1) p2 == set_array_perm a p2)
= ()

let set_array_perm_eq
  (#t: Type)
  (a: array t)
: Lemma
  (set_array_perm a (array_perm a) == a)
= ()

let set_array_perm_adjacent
  (#t: Type)
  (a1 a2: array t)
  (p: perm)
: Lemma
  (requires (adjacent a1 a2))
  (ensures (
    merge_into (set_array_perm a1 p) (set_array_perm a2 p) (set_array_perm (merge a1 a2) p)
  ))
= ()

#set-options "--ide_id_info_off"

let share
  (#opened: _)
  (#elt: Type)
  (#x: v elt)
  (a: t elt)
  (p1 p2: perm)
: STGhost (Ghost.erased (v elt & v elt)) opened
    (arrayptr a x)
    (fun res -> arrayptr a (fst res) `star` arrayptr a (snd res))
    (array_perm (array_of x) == p1 `Steel.FractionalPermission.sum_perm` p2)
    (fun res ->
      contents_of' (fst res) == contents_of x /\
      contents_of' (snd res) == contents_of x /\
      array_of (fst res) == set_array_perm (array_of x) p1 /\
      array_of (snd res) == set_array_perm (array_of x) p2
    )
=
  rewrite (arrayptr a x) (arrayptr0 a x);
  let _ = gen_elim () in
  vpattern_rewrite (STC.array_pts_to _) _;
  STC.mk_fraction_seq_split_gen _ (mk_full_scalar_seq x.v_contents) x.v_array.array_perm p1 p2;
  let res1 = {
    v_array = set_array_perm x.v_array p1;
    v_contents = x.v_contents;
  }
  in
  let res2 = {
    v_array = set_array_perm x.v_array p2;
    v_contents = x.v_contents;
  }
  in
  let res = Ghost.hide (res1, res2) in
  let s = vpattern_replace (fun s -> STC.array_pts_to _ s `star` STC.array_pts_to _ (STC.mk_fraction_seq _ _ p2)) in
  rewrite (STC.array_pts_to _ s) (arrayptr1 (fst res) s);
  rewrite (arrayptr0 a (fst res)) (arrayptr a (fst res));
  let s = vpattern_replace (STC.array_pts_to _) in
  rewrite (STC.array_pts_to _ _) (arrayptr1 (snd res) s);
  rewrite (arrayptr0 a (snd res)) (arrayptr a (snd res));
  res

let gather
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: v elt)
  (a: t elt)
: STGhost (v elt) opened
    (arrayptr a x1 `star` arrayptr a x2)
    (fun res -> arrayptr a res)
    (array_of x1 == set_array_perm (array_of x2) (array_perm (array_of x1)))
    (fun res ->
      contents_of' res == contents_of x1 /\
      contents_of' res == contents_of x2 /\
      array_of res == set_array_perm (array_of x1) (array_perm (array_of x1) `Steel.FractionalPermission.sum_perm` array_perm (array_of x2))
    )
= rewrite (arrayptr a x1) (arrayptr0 a x1);
  let _ = gen_elim () in
  rewrite (STC.array_pts_to _ _) (STC.array_pts_to x1.v_array.array_ptr (STC.mk_fraction_seq (STC.scalar elt) (mk_full_scalar_seq x1.v_contents) x1.v_array.array_perm));
  rewrite (arrayptr a x2) (arrayptr0 a x2);
  let _ = gen_elim () in
  rewrite
    (STC.array_pts_to x2.v_array.array_ptr _)
    (STC.array_pts_to x1.v_array.array_ptr (STC.mk_fraction_seq (STC.scalar elt) (mk_full_scalar_seq x2.v_contents) x2.v_array.array_perm));
  STC.array_fractional_permissions_theorem (mk_full_scalar_seq x1.v_contents) (mk_full_scalar_seq x2.v_contents) x1.v_array.array_perm x2.v_array.array_perm x1.v_array.array_ptr;
  rewrite
    (STC.array_pts_to x1.v_array.array_ptr (STC.mk_fraction_seq (STC.scalar elt) (mk_full_scalar_seq x2.v_contents) x2.v_array.array_perm))
    (STC.array_pts_to x1.v_array.array_ptr (STC.mk_fraction_seq (STC.scalar elt) (mk_full_scalar_seq x1.v_contents) x2.v_array.array_perm));
  STC.mk_fraction_seq_join x1.v_array.array_ptr (mk_full_scalar_seq x1.v_contents) x1.v_array.array_perm x2.v_array.array_perm;
  let s = vpattern_replace (STC.array_pts_to _) in
  let res = {
    v_array = set_array_perm x1.v_array (x1.v_array.array_perm `Steel.FractionalPermission.sum_perm` x2.v_array.array_perm);
    v_contents = x1.v_contents;
  }
  in
  let prf
    (i: nat)
  : Lemma
    (requires (i < length x1.v_array))
    (ensures (
      i < length x1.v_array /\
      Seq.index x1.v_contents i == Seq.index x2.v_contents i
    ))
  = STC.mk_scalar_inj (Seq.index x1.v_contents i) (Seq.index x2.v_contents i) full_perm full_perm
  in
  Classical.forall_intro (Classical.move_requires prf);
  assert (x2.v_contents `Seq.equal` x1.v_contents);
  rewrite (STC.array_pts_to _ _) (arrayptr1 res s);
  rewrite (arrayptr0 a res) (arrayptr a res);
  res
