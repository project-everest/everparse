module CBOR.Spec.Raw.DataModel

include CBOR.Spec.Constants

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module FS = FStar.FiniteSet.Base
module FSA = FStar.FiniteSet.Ambient
module U = CBOR.Spec.Util

open CBOR.Spec.Raw.Base

val cbor
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    CBOR.Spec.Raw.Sort.compare_prop order compare
  })
: eqtype

(** CBOR maps *)

val cbor_map
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    CBOR.Spec.Raw.Sort.compare_prop order compare
  })
: eqtype

val cbor_map_get #order #compare: cbor_map order compare -> cbor order compare -> Tot (option (cbor order compare))

let cbor_map_defined #order #compare (k: cbor order compare) (f: cbor_map order compare) : Tot bool =
  Some? (cbor_map_get f k)

val cbor_map_get_precedes #order #compare (m: cbor_map order compare) (x: cbor order compare) : Lemma
  (ensures (match cbor_map_get m x with
  | None -> True
  | Some y -> (x << m) /\ (y << m)
  ))
  [SMTPat (cbor_map_get m x)]

let cbor_map_equal #order #compare (m1 m2: cbor_map order compare) : Tot prop =
  (forall k . cbor_map_get m1 k == cbor_map_get m2 k)

val cbor_map_ext #order #compare: (m1: cbor_map order compare) -> (m2: cbor_map order compare) -> Lemma
  (ensures (cbor_map_equal m1 m2 <==> m1 == m2))
  [SMTPat (cbor_map_equal m1 m2)]

val cbor_map_set_keys #order #compare: (m: cbor_map order compare) -> FS.set (cbor order compare)

val cbor_map_set_keys_mem #order #compare: (m: cbor_map order compare) -> (k: cbor order compare) -> Lemma
  (FS.mem k (cbor_map_set_keys m) <==> cbor_map_defined k m)
  [SMTPat (FS.mem k (cbor_map_set_keys m))]

val cbor_map_length #order #compare (m: cbor_map order compare) : Pure nat
  (requires True)
  (ensures (fun n -> n == FS.cardinality (cbor_map_set_keys m)))

val cbor_map_empty #order #compare: cbor_map order compare

val cbor_map_get_empty #order #compare: (k: cbor order compare) -> Lemma
  (ensures (cbor_map_get cbor_map_empty k == None))
  [SMTPat (cbor_map_get cbor_map_empty k)]

let cbor_map_set_keys_empty #order #compare : squash (cbor_map_set_keys (cbor_map_empty #order #compare) == FS.emptyset) =
  assert (cbor_map_set_keys (cbor_map_empty #order #compare) `FS.equal` FS.emptyset)

let cbor_map_length_empty #order #compare: squash (cbor_map_length (cbor_map_empty #order #compare) == 0) = ()

val cbor_map_singleton #order #compare: cbor order compare -> cbor order compare -> cbor_map order compare

val cbor_map_get_singleton #order #compare: (k: cbor order compare) -> (v: cbor order compare) -> (k': cbor order compare) -> Lemma
  (ensures (cbor_map_get (cbor_map_singleton k v) k' == (if k = k' then Some v else None)))
  [SMTPat (cbor_map_get (cbor_map_singleton k v) k')]

let cbor_map_set_keys_singleton #order #compare (k: cbor order compare) (v: cbor order compare) : Lemma
  (ensures (cbor_map_set_keys (cbor_map_singleton k v) == FS.singleton k))
  [SMTPat (cbor_map_set_keys (cbor_map_singleton k v))]
= assert (cbor_map_set_keys (cbor_map_singleton k v) `FS.equal` FS.singleton k)

let cbor_map_length_singleton #order #compare (k: cbor order compare) (v: cbor order compare) : Lemma
  (ensures (cbor_map_length (cbor_map_singleton k v) == 1))
= ()

val cbor_map_filter #order #compare:
  ((cbor order compare & cbor order compare) -> bool) ->
  cbor_map order compare ->
  cbor_map order compare

val cbor_map_get_filter #order #compare: (f: (cbor order compare & cbor order compare -> bool)) -> (m: cbor_map order compare) -> (k: cbor order compare) -> Lemma
  (ensures (cbor_map_get (cbor_map_filter f m) k == begin match cbor_map_get m k with
  | None -> None
  | Some v -> if f (k, v) then Some v else None
  end))
  [SMTPat (cbor_map_get (cbor_map_filter f m) k)]

val cbor_map_length_filter
  #order #compare
  (f: ((cbor order compare & cbor order compare) -> bool))
  (m: cbor_map order compare)
: Lemma
  (ensures (cbor_map_length (cbor_map_filter f m) <= cbor_map_length m))
  [SMTPat (cbor_map_length (cbor_map_filter f m))]

val cbor_map_union #order #compare: cbor_map order compare -> cbor_map order compare -> cbor_map order compare

val cbor_map_get_union #order #compare: (m1: cbor_map order compare) -> (m2: cbor_map order compare) -> (k: cbor order compare) -> Lemma
  (ensures (cbor_map_get (cbor_map_union m1 m2) k == begin match cbor_map_get m1 k with
    | None -> cbor_map_get m2 k
    | v -> v
    end
  ))
  [SMTPat (cbor_map_get (cbor_map_union m1 m2) k)]

let cbor_map_set_keys_union #order #compare (m1 m2: cbor_map order compare) : Lemma
  (ensures (cbor_map_set_keys (cbor_map_union m1 m2) == (cbor_map_set_keys m1 `FS.union` cbor_map_set_keys m2)))
  [SMTPat (cbor_map_set_keys (cbor_map_union m1 m2))]
= assert (cbor_map_set_keys (cbor_map_union m1 m2) `FS.equal` (cbor_map_set_keys m1 `FS.union` cbor_map_set_keys m2))

let cbor_map_disjoint #order #compare (m1 m2: cbor_map order compare) : Tot prop =
  forall k . ~ (cbor_map_defined k m1 /\ cbor_map_defined k m2)

let cbor_map_length_disjoint_union #order #compare (m1 m2: cbor_map order compare) : Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures (
    cbor_map_length (cbor_map_union m1 m2) == cbor_map_length m1 + cbor_map_length m2
  ))
= 
  assert (FS.intersection (cbor_map_set_keys m1) (cbor_map_set_keys m2) `FS.equal` FS.emptyset);
  assert (FS.cardinality (FS.union (cbor_map_set_keys m1) (cbor_map_set_keys m2)) == FS.cardinality (cbor_map_set_keys m1) + FS.cardinality (cbor_map_set_keys m2))

let cbor_map_mem #order #compare (kv: (cbor order compare & cbor order compare)) (f: cbor_map order compare) : Tot bool =
  cbor_map_get f (fst kv) = Some (snd kv)

let cbor_map_defined_alt
  #order #compare
  (k: cbor order compare) (f: cbor_map order compare)
: Lemma
  (cbor_map_defined k f <==> (exists v . cbor_map_mem (k, v) f))
  [SMTPat (cbor_map_defined k f)]
= match cbor_map_get f k with
  | None -> ()
  | Some _ -> ()

let cbor_map_union_assoc #order #compare (m1 m2 m3: cbor_map order compare) : Lemma
  (cbor_map_union (cbor_map_union m1 m2) m3 == cbor_map_union m1 (cbor_map_union m2 m3))
= cbor_map_ext
    (cbor_map_union (cbor_map_union m1 m2) m3)
    (cbor_map_union m1 (cbor_map_union m2 m3))

let cbor_map_union_empty_l #order #compare (m: cbor_map order compare) : Lemma
  (cbor_map_union cbor_map_empty m == m)
  [SMTPat (cbor_map_union cbor_map_empty m)]
= cbor_map_ext (cbor_map_union cbor_map_empty m) m

let cbor_map_union_empty_r #order #compare (m: cbor_map order compare) : Lemma
  (cbor_map_union m cbor_map_empty == m)
  [SMTPat (cbor_map_union m cbor_map_empty)]
= cbor_map_ext (cbor_map_union m cbor_map_empty) m

let cbor_map_disjoint_mem_union #order #compare (m1 m2: cbor_map order compare) (xv: (cbor order compare & cbor order compare)) : Lemma
  (requires cbor_map_disjoint m1 m2)
  (ensures cbor_map_mem xv (m1 `cbor_map_union` m2) <==> cbor_map_mem xv m1 \/ cbor_map_mem xv m2)
= ()

let cbor_map_disjoint_mem_union' #order #compare (m1 m2: cbor_map order compare) (_: squash (cbor_map_disjoint m1 m2)) : Lemma
  (ensures forall xv . cbor_map_mem xv (m1 `cbor_map_union` m2) <==> cbor_map_mem xv m1 \/ cbor_map_mem xv m2)
= ()

let cbor_map_disjoint_union_comm #order #compare (m1 m2: cbor_map order compare) : Lemma
  (requires cbor_map_disjoint m1 m2)
  (ensures m1 `cbor_map_union` m2 == m2 `cbor_map_union` m1)
  [SMTPat (m1 `cbor_map_union` m2)]
= cbor_map_disjoint_mem_union' m1 m2 ();
  cbor_map_disjoint_mem_union' m2 m1 ();
  cbor_map_ext (m1 `cbor_map_union` m2) (m2 `cbor_map_union` m1)

let cbor_map_mem_filter
  #order #compare
  (f: (cbor order compare & cbor order compare) -> Tot bool)
  (m: cbor_map order compare)
  (x: (cbor order compare & cbor order compare))
: Lemma
  (cbor_map_mem x (cbor_map_filter f m) <==> cbor_map_mem x m /\ f x)
  [SMTPat (cbor_map_mem x (cbor_map_filter f m))]
= ()

let cbor_map_filter_for_all
  #order #compare
  (f: (cbor order compare & cbor order compare) -> Tot bool)
  (m: cbor_map order compare)
: Lemma
  (requires forall x . cbor_map_mem x m ==> f x)
  (ensures cbor_map_filter f m == m)
= cbor_map_ext (cbor_map_filter f m) m

let cbor_map_filter_for_all'
  #order #compare
  (f: (cbor order compare & cbor order compare) -> Tot bool)
  (m: cbor_map order compare)
  (sq: squash (forall x . cbor_map_mem x m ==> f x))
: Lemma
  (ensures cbor_map_filter f m == m)
= cbor_map_filter_for_all f m

let cbor_map_filter_ext
  #order #compare
  (f1 f2: (cbor order compare & cbor order compare) -> Tot bool)
  (m: cbor_map order compare)
: Lemma
  (requires forall x . f1 x == f2 x)
  (ensures cbor_map_filter f1 m == cbor_map_filter f2 m)
= cbor_map_ext (cbor_map_filter f1 m) (cbor_map_filter f2 m)

let cbor_map_disjoint_union_filter
  #order #compare
  (f: (cbor order compare & cbor order compare) -> Tot bool)
  (m1 m2: cbor_map order compare)
: Lemma
  (requires cbor_map_disjoint m1 m2)
  (ensures (cbor_map_filter f (cbor_map_union m1 m2) == cbor_map_filter f m1 `cbor_map_union` cbor_map_filter f m2))
= cbor_map_ext
    (cbor_map_filter f (cbor_map_union m1 m2))
    (cbor_map_filter f m1 `cbor_map_union` cbor_map_filter f m2)

let cbor_map_disjoint_union_filter'
  #order #compare
  (f: (cbor order compare & cbor order compare) -> Tot bool)
  (m1 m2: cbor_map order compare)
  (sq: squash (cbor_map_disjoint m1 m2))
: Lemma
  (ensures (cbor_map_filter f (cbor_map_union m1 m2) == cbor_map_filter f m1 `cbor_map_union` cbor_map_filter f m2))
= cbor_map_disjoint_union_filter f m1 m2

let cbor_map_filter_filter
  #order #compare
  (p1 p2: (cbor order compare & cbor order compare) -> Tot bool)
  (f: cbor_map order compare)
: Lemma
  (cbor_map_filter p2 (cbor_map_filter p1 f) == cbor_map_filter (p1 `U.andp` p2) f)
= cbor_map_ext
    (cbor_map_filter p2 (cbor_map_filter p1 f))
    (cbor_map_filter (p1 `U.andp` p2) f)

let cbor_map_filter_implies
  #order #compare
  (p1 p2: (cbor order compare & cbor order compare) -> Tot bool)
  (f: cbor_map order compare)
: Lemma
  (requires (forall kv . p1 kv ==> p2 kv))
  (ensures (cbor_map_filter p2 (cbor_map_filter p1 f) == cbor_map_filter p1 f))
= cbor_map_filter_filter p1 p2 f;
  cbor_map_filter_ext p1 (p1 `U.andp` p2) f

let cbor_map_split
  #order #compare
  (f: (cbor order compare & cbor order compare) -> Tot bool)
  (m: cbor_map order compare)
: Lemma (
    let mtrue = cbor_map_filter f m in
    let mfalse = cbor_map_filter (U.notp f) m in
    mtrue `cbor_map_disjoint` mfalse /\
    mtrue `cbor_map_union` mfalse == m
  )
= let mtrue = cbor_map_filter f m in
  let mfalse = cbor_map_filter (U.notp f) m in
  assert (mtrue `cbor_map_disjoint` mfalse);
  cbor_map_ext (mtrue `cbor_map_union` mfalse) m

let cbor_map_equal' #order #compare (f1 f2: cbor_map order compare) : Tot prop
= forall kv . cbor_map_mem kv f1 <==> cbor_map_mem kv f2

let cbor_map_equiv #order #compare (f1 f2: cbor_map order compare) : Lemma
  (requires cbor_map_equal' f1 f2)
  (ensures f1 == f2)
  [SMTPat (cbor_map_equal' f1 f2)]
= let prf
    (k: cbor order compare)
  : Lemma
    (cbor_map_get f1 k == cbor_map_get f2 k)
  = match cbor_map_get f1 k with
    | Some v1 -> assert (cbor_map_mem (k, v1) f2)
    | _ ->
      begin match cbor_map_get f2 k with
      | Some v2 -> assert (cbor_map_mem (k, v2) f1)
      | _ -> ()
      end
  in
  Classical.forall_intro prf;
  assert (cbor_map_equal f1 f2)

#restart-solver
let cbor_map_disjoint_union_simpl_l
  #order #compare
  (g g1 g2: cbor_map order compare)
: Lemma
  (requires
    g `cbor_map_disjoint` g1 /\
    g `cbor_map_disjoint` g2 /\
    g `cbor_map_union` g1 == g `cbor_map_union` g2
  )
  (ensures g1 == g2)
= assert (forall x . cbor_map_mem x g1 <==> (cbor_map_mem x (g `cbor_map_union` g1) /\ ~ (cbor_map_mem x g)));
  cbor_map_equiv g1 g2

#restart-solver
let cbor_map_disjoint_union_simpl_r
  #order #compare
  (g1 g2 g: cbor_map order compare)
: Lemma
  (requires
    g1 `cbor_map_disjoint` g /\
    g2 `cbor_map_disjoint` g /\
    g1 `cbor_map_union` g == g2 `cbor_map_union` g
  )
  (ensures g1 == g2)
= cbor_map_disjoint_union_comm g1 g;
  cbor_map_disjoint_union_comm g2 g;
  cbor_map_disjoint_union_simpl_l g g1 g2

let cbor_map_included
  #order #compare
  (m1 m2: cbor_map order compare)
: Tot prop
= forall x . cbor_map_mem x m1 ==> cbor_map_mem x m2

let cbor_map_sub
  #order #compare
  (m1 m2: cbor_map order compare)
: Pure (cbor_map order compare)
    (requires cbor_map_included m2 m1)
    (ensures fun m3 ->
      m2 `cbor_map_disjoint` m3 /\
      m2 `cbor_map_union` m3 == m1
    )
= let phi (kv: (cbor order compare & cbor order compare)) : Tot bool = not (cbor_map_mem kv m2) in
  let m3 = cbor_map_filter phi m1 in
  assert (cbor_map_disjoint m2 m3);
  cbor_map_disjoint_mem_union' m2 m3 ();
  cbor_map_equiv (cbor_map_union m2 m3) m1;
  m3

val cbor_map_key_list #order #compare (m: cbor_map order compare) : GTot (list (cbor order compare))

val cbor_map_key_list_mem #order #compare (m: cbor_map order compare) (k: cbor order compare) : Lemma
  (ensures (List.Tot.memP k (cbor_map_key_list m) <==> cbor_map_defined k m))
  [SMTPat (List.Tot.memP k (cbor_map_key_list m))]

val cbor_map_key_list_no_repeats_p #order #compare (m: cbor_map order compare) : Lemma
  (ensures (List.Tot.no_repeats_p (cbor_map_key_list m)))
  [SMTPat (cbor_map_key_list m)]

val cbor_map_key_list_length #order #compare (m: cbor_map order compare) : Lemma
  (ensures (List.Tot.length (cbor_map_key_list m) == cbor_map_length m))
  [SMTPat (List.Tot.length (cbor_map_key_list m))]

let cbor_map_length_empty_equiv
  #order #compare
  (m: cbor_map order compare)
: Lemma
  (cbor_map_length m == 0 <==> m == cbor_map_empty)
= cbor_map_key_list_length m;
  match cbor_map_key_list m with
  | [] -> cbor_map_equiv m cbor_map_empty
  | a :: q -> cbor_map_key_list_mem m a

let cbor_map_disjoint_tot
  #order #compare
  (m1 m2: cbor_map order compare)
: Pure bool
    (requires True)
    (ensures fun b -> b <==> cbor_map_disjoint m1 m2)
= let f (xy: (cbor order compare & cbor order compare )) : Tot bool = cbor_map_defined (fst xy) m2 in
  let m1' = cbor_map_filter f m1 in
  cbor_map_key_list_length m1';
  assert (Nil? (cbor_map_key_list m1') ==> cbor_map_equal m1' cbor_map_empty);
  m1' = cbor_map_empty

val cbor_map_fold
  #order #compare
  (#a: Type)
  (f: a -> cbor order compare -> a)
  (x: a)
  (m: cbor_map order compare)
: Tot a

val cbor_map_fold_ext
  #order #compare
  (#a: Type)
  (f1 f2: a -> cbor order compare -> a)
  (x: a)
  (m1 m2: cbor_map order compare)
: Lemma
  (requires (
    (forall (x: a) (y: cbor order compare) . cbor_map_defined y m1 ==> f1 x y == f2 x y) /\
    (forall (x: cbor order compare) . cbor_map_defined x m1 <==> cbor_map_defined x m2)
  ))
  (ensures (cbor_map_fold f1 x m1 == cbor_map_fold f2 x m2))

val cbor_map_fold_eq
  #order #compare
  (#a: Type)
  (f: a -> cbor order compare -> a)
  (x: a)
  (m: cbor_map order compare)
  (l: list (cbor order compare))
: Lemma
  (requires (
    U.op_comm f /\
    (forall (x: cbor order compare) . List.Tot.memP x l <==> cbor_map_defined x m) /\
    List.Tot.no_repeats_p l
  ))
  (ensures (
    cbor_map_fold f x m == List.Tot.fold_left f x l
  ))

val cbor_map_fold_eq_idem
  #order #compare
  (#a: Type)
  (f: a -> cbor order compare -> a)
  (x: a)
  (m: cbor_map order compare)
  (l: list (cbor order compare))
: Lemma
  (requires (
    U.op_comm f /\
    U.op_idem f /\
    (forall (x: cbor order compare) . List.Tot.memP x l <==> cbor_map_defined x m)
  ))
  (ensures (
    cbor_map_fold f x m == List.Tot.fold_left f x l
  ))

let cbor_map_fold_empty
  #order #compare
  (#a: Type)
  (f: a -> cbor order compare -> a {
    U.op_comm f
  })
  (x: a)
: Lemma
  (cbor_map_fold f x cbor_map_empty == x)
= cbor_map_fold_eq f x cbor_map_empty []

let cbor_map_fold_singleton
  #order #compare
  (#a: Type)
  (f: a -> cbor order compare -> a {
    U.op_comm f
  })
  (x: a)
  (key value: cbor order compare)
: Lemma
  (cbor_map_fold f x (cbor_map_singleton key value) == f x key)
= cbor_map_fold_eq f x (cbor_map_singleton key value) [key]

let cbor_map_fold_union
  #order #compare
  (#a: Type)
  (f: a -> cbor order compare -> a {
    U.op_comm f
  })
  (x: a)
  (m1 m2: cbor_map order compare)
: Lemma
  (requires (
    cbor_map_disjoint m1 m2
  ))
  (ensures (
    cbor_map_fold f x (cbor_map_union m1 m2) ==
      cbor_map_fold f (cbor_map_fold f x m1) m2
  ))
= let l1 = cbor_map_key_list m1 in
  let l2 = cbor_map_key_list m2 in
  List.Tot.append_memP_forall l1 l2;
  List.Tot.no_repeats_p_append l1 l2;
  cbor_map_fold_eq f x (cbor_map_union m1 m2) (List.Tot.append l1 l2);
  cbor_map_fold_eq f x m1 l1;
  cbor_map_fold_eq f (cbor_map_fold f x m1) m2 l2;
  U.list_fold_append f x l1 l2

let cbor_map_singleton_elim
  #order #compare
  (s: cbor_map order compare)
: Pure (cbor order compare & cbor order compare)
    (requires cbor_map_length s == 1)
    (ensures fun x -> cbor_map_equal s (cbor_map_singleton (fst x) (snd x)))
= let l = Ghost.hide (cbor_map_key_list s) in
  assert (forall x . List.Tot.memP x l <==> cbor_map_defined x s);
  assert (List.Tot.length l == 1);
  assert (forall x . cbor_map_defined x s <==> x == List.Tot.hd l);
  let t = (x: cbor order compare { cbor_map_defined x s }) in
  let f (accu: option t) (x: cbor order compare) : Tot (option t) =
    if cbor_map_defined x s
    then Some x
    else accu
  in
  cbor_map_fold_eq f None s l;
  let ores : option t = cbor_map_fold f None s in
  assert (Some? ores);
  let k = Some?.v ores in
  let Some v = cbor_map_get s k in
  (k, v)

(** CBOR objects *)

type cbor_case order compare =
  | CSimple: (v: simple_value) -> cbor_case order compare
  | CInt64: (typ: major_type_uint64_or_neg_int64) -> (v: U64.t) -> cbor_case order compare
  | CString: (typ: major_type_byte_string_or_text_string) -> (v: Seq.seq U8.t { FStar.UInt.fits (Seq.length v) U64.n /\ (typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) }) -> cbor_case order compare
  | CArray: (v: list (cbor order compare) { FStar.UInt.fits (List.Tot.length v) U64.n }) -> cbor_case order compare
  | CMap: (c: cbor_map order compare { FStar.UInt.fits (cbor_map_length c) U64.n }) -> cbor_case order compare
  | CTagged: (tag: U64.t) -> (v: cbor order compare) -> cbor_case order compare

val unpack #order #compare: cbor order compare -> cbor_case order compare

val pack #order #compare: cbor_case order compare -> cbor order compare

val unpack_pack #order #compare: (c: cbor_case order compare) -> Lemma
  (ensures (unpack (pack c) == c))
  [SMTPat (pack c)]

val pack_unpack #order #compare: (c: cbor order compare) -> Lemma
  (ensures (pack (unpack c) == c))
  [SMTPat (unpack c)]

val unpack_precedes
  #order #compare
  (c: cbor order compare)
: Lemma
  (ensures (match unpack c with
  | CArray v -> (forall x . List.Tot.memP x v ==> x << c) // (v << c DOES NOT hold because of casting between the refinement on the list and the refinement on all its elements)
  | CMap v -> v << c
  | CTagged _ v -> v << c
  | _ -> True
  ))
  [SMTPat (unpack c)]

val size
  #order #compare
  (c: cbor order compare)
: nat

val size_unpack
  #order #compare
  (c: cbor order compare)
: Lemma
  (match unpack c with
  | CArray v -> (forall x . List.Tot.memP x v ==> size x < size c)
  | CMap v -> (forall x . cbor_map_mem x v ==> (size (fst x) < size c /\ size (snd x) < size c))
  | CTagged _ v -> size v < size c
  | _ -> True
  )
