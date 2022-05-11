module LowParse.SteelST.ArrayPtr
module SAS = Steel.ST.ArraySlice
module U32 = FStar.UInt32

let t elt = SAS.array_slice elt

[@@erasable]
noeq
type array elt = {
  array_ptr: SAS.array_slice elt;
  array_len: (len: U32.t { SAS.offset array_ptr + U32.v len <= SAS.base_length array_ptr });
  array_perm: Steel.FractionalPermission.perm;
  array_base_len: (len: U32.t { U32.v len == SAS.base_length array_ptr });
}

let len x = SZ.mk_size_t x.array_len

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

[@__reduce__]
let arrayptr0 (#elt: _) (r: t elt) (v: v elt) : Tot vprop =
  exists_ (fun tbl -> SAS.pts_to r v.v_array.array_perm tbl `star` pure (
    v.v_array.array_ptr == r /\
    U32.v v.v_array.array_len == Seq.length tbl /\
    tbl == v.v_contents
  ))

let arrayptr r v = arrayptr0 r v
    
let adjacent x1 x2 =
  x1.array_perm == x2.array_perm /\
  SAS.has_ptr_diff x2.array_ptr x1.array_ptr (U32.v x1.array_len)

let merge x1 x2 = {
  array_ptr = x1.array_ptr;
  array_len = x1.array_len `U32.add` x2.array_len;
  array_perm = x1.array_perm;
  array_base_len = x1.array_base_len;
}

let merge_assoc1
  (#t: Type0)
  (x1 x2 x3: array t)
: Lemma
  (requires (
    (adjacent x1 x2 /\ adjacent (merge x1 x2) x3)
  ))
  (ensures (
    adjacent x1 x2 /\ adjacent (merge x1 x2) x3 /\
    adjacent x2 x3 /\ adjacent x1 (merge x2 x3) /\
    merge (merge x1 x2) x3 == merge x1 (merge x2 x3)
  ))
= SAS.ptr_le_interpolate x1.array_ptr x2.array_ptr x3.array_ptr

let merge_assoc2
  (#t: Type0)
  (x1 x2 x3: array t)
: Lemma
  (requires (
    (adjacent x2 x3 /\ adjacent x1 (merge x2 x3))
  ))
  (ensures (
    adjacent x1 x2 /\ adjacent (merge x1 x2) x3 /\
    adjacent x2 x3 /\ adjacent x1 (merge x2 x3) /\
    merge (merge x1 x2) x3 == merge x1 (merge x2 x3)
  ))
= SAS.ptr_le_trans x1.array_ptr x2.array_ptr x3.array_ptr

let merge_assoc x1 x2 x3 =
  Classical.move_requires (merge_assoc1 x1 x2) x3;
  Classical.move_requires (merge_assoc2 x1 x2) x3

let join #_ #a #vl #vr al ar =
  rewrite (arrayptr al vl) (arrayptr0 al vl);
  rewrite (arrayptr ar vr) (arrayptr0 ar vr);
  let _ = gen_elim () in
  SAS.join al ar;
  let res = {
    v_array = merge (array_of vl) (array_of vr);
    v_contents = Seq.append vl.v_contents vr.v_contents;
  }
  in
  rewrite (arrayptr0 al res) (arrayptr al res);
  res

#push-options "--z3rlimit 16"

let gsplit #_ #_ #v x i =
  rewrite (arrayptr x v) (arrayptr0 x v);
  let _ = gen_elim () in
  let i' = SZ.uint32_of_size_t i (U32.uint_to_t (SZ.size_v i)) in
  let res = SAS.ghost_split x i' in
  let _ = gen_elim () in
  let vl_array = {
    array_ptr = x;
    array_len = i';
    array_perm = v.v_array.array_perm;
    array_base_len = v.v_array.array_base_len;
  }
  in
  let vl = {
    v_array = vl_array;
    v_contents = Seq.slice v.v_contents 0 (U32.v i');
  }
  in
  let vr_array = {
    array_ptr = res;
    array_len = v.v_array.array_len `U32.sub` i';
    array_perm = v.v_array.array_perm;
    array_base_len = v.v_array.array_base_len;
  }
  in
  let vr = {
    v_array = vr_array;
    v_contents = Seq.slice v.v_contents (U32.v i') (Seq.length v.v_contents);
  }
  in
  noop ();
  rewrite (arrayptr0 x vl) (arrayptr x vl);
  rewrite (arrayptr0 res vr) (arrayptr res vr);
  let _ = merge vl_array vr_array in // FIXME: WHY WHY WHY?
  noop ();
  res

#pop-options

let split' #_ #_ #vl #vr x i x' =
  let i' = SZ.uint32_of_size_t i (U32.uint_to_t (SZ.size_v i)) in
  rewrite (arrayptr x vl) (arrayptr0 x vl);
  rewrite (arrayptr x' vr) (arrayptr0 x' vr);
  let _ = gen_elim () in
  let res = SAS.ptr_shift x i' in
  SAS.has_ptr_diff_inj x' x (SZ.size_v i) res; 
  rewrite (arrayptr0 x vl) (arrayptr x vl);
  rewrite (arrayptr0 x' vr) (arrayptr x' vr);
  rewrite (arrayptr x'  vr) (arrayptr res vr);
  return res

let index #_ #v r i =
  rewrite (arrayptr r v) (arrayptr0 r v);
  let _ = gen_elim () in
  let res = SAS.read r (SZ.uint32_of_size_t i (U32.uint_to_t (SZ.size_v i))) in
  rewrite (arrayptr0 r v) (arrayptr r v);
  return res

let upd #elt #v r i x =
  rewrite (arrayptr r v) (arrayptr0 r v);
  let _ = gen_elim () in
  let i' = SZ.uint32_of_size_t i (U32.uint_to_t (SZ.size_v i)) in
  let _ = vpattern_replace_erased (fun s -> SAS.pts_to r _ s) in
  let s' = SAS.write r i' x in
  let res = {
    v_array = v.v_array;
    v_contents = s';
  }
  in
  noop ();
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
= rewrite (arrayptr a x) (arrayptr0 a x);
  let _ = gen_elim () in
  let _ = SAS.share a _ p1 p2 in
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
  rewrite (arrayptr0 a (fst res)) (arrayptr a (fst res));
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
  rewrite (arrayptr a x2) (arrayptr0 a x2);
  let _ = gen_elim () in
  SAS.gather a x1.v_array.array_perm x2.v_array.array_perm;
  let res = {
    v_array = set_array_perm x1.v_array (x1.v_array.array_perm `Steel.FractionalPermission.sum_perm` x2.v_array.array_perm);
    v_contents = x1.v_contents;
  }
  in
  rewrite (arrayptr0 a res) (arrayptr a res);
  res
