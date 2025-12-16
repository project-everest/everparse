(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module CBOR.Spec.API.Type
include CBOR.Spec.Constants

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module FS = FStar.FiniteSet.Base
module FSA = FStar.FiniteSet.Ambient
module U = CBOR.Spec.Util

(* The generic data model *)

val cbor: eqtype

(** CBOR maps *)

val cbor_map: eqtype

val cbor_map_get: cbor_map -> cbor -> Tot (option cbor)

let cbor_map_defined (k: cbor) (f: cbor_map) : Tot bool =
  Some? (cbor_map_get f k)

val cbor_map_get_precedes (m: cbor_map) (x: cbor) : Lemma
  (ensures (match cbor_map_get m x with
  | None -> True
  | Some y -> (x << m) /\ (y << m)
  ))
  [SMTPat (cbor_map_get m x)]

let cbor_map_equal (m1 m2: cbor_map) : Tot prop =
  (forall k . cbor_map_get m1 k == cbor_map_get m2 k)

val cbor_map_ext: (m1: cbor_map) -> (m2: cbor_map) -> Lemma
  (ensures (cbor_map_equal m1 m2 <==> m1 == m2))
  [SMTPat (cbor_map_equal m1 m2)]

val cbor_map_set_keys: (m: cbor_map) -> FS.set cbor

val cbor_map_set_keys_mem: (m: cbor_map) -> (k: cbor) -> Lemma
  (FS.mem k (cbor_map_set_keys m) <==> cbor_map_defined k m)
  [SMTPat (FS.mem k (cbor_map_set_keys m))]

val cbor_map_length (m: cbor_map) : Pure nat
  (requires True)
  (ensures (fun n -> n == FS.cardinality (cbor_map_set_keys m)))

val cbor_map_empty: cbor_map

val cbor_map_get_empty: (k: cbor) -> Lemma
  (ensures (cbor_map_get cbor_map_empty k == None))
  [SMTPat (cbor_map_get cbor_map_empty k)]

let cbor_map_set_keys_empty : squash (cbor_map_set_keys cbor_map_empty == FS.emptyset) =
  assert (cbor_map_set_keys cbor_map_empty `FS.equal` FS.emptyset)

let cbor_map_length_empty: squash (cbor_map_length cbor_map_empty == 0) = ()

val cbor_map_singleton: cbor -> cbor -> cbor_map

val cbor_map_get_singleton: (k: cbor) -> (v: cbor) -> (k': cbor) -> Lemma
  (ensures (cbor_map_get (cbor_map_singleton k v) k' == (if k = k' then Some v else None)))
  [SMTPat (cbor_map_get (cbor_map_singleton k v) k')]

let cbor_map_set_keys_singleton (k: cbor) (v: cbor) : Lemma
  (ensures (cbor_map_set_keys (cbor_map_singleton k v) == FS.singleton k))
  [SMTPat (cbor_map_set_keys (cbor_map_singleton k v))]
= assert (cbor_map_set_keys (cbor_map_singleton k v) `FS.equal` FS.singleton k)

let cbor_map_length_singleton (k: cbor) (v: cbor) : Lemma
  (ensures (cbor_map_length (cbor_map_singleton k v) == 1))
= ()

val cbor_map_filter:
  ((cbor & cbor) -> bool) ->
  cbor_map ->
  cbor_map

val cbor_map_get_filter: (f: (cbor & cbor -> bool)) -> (m: cbor_map) -> (k: cbor) -> Lemma
  (ensures (cbor_map_get (cbor_map_filter f m) k == begin match cbor_map_get m k with
  | None -> None
  | Some v -> if f (k, v) then Some v else None
  end))
  [SMTPat (cbor_map_get (cbor_map_filter f m) k)]

val cbor_map_length_filter
  (f: ((cbor & cbor) -> bool))
  (m: cbor_map)
: Lemma
  (ensures (cbor_map_length (cbor_map_filter f m) <= cbor_map_length m))
  [SMTPat (cbor_map_length (cbor_map_filter f m))]

val cbor_map_union: cbor_map -> cbor_map -> cbor_map

val cbor_map_get_union: (m1: cbor_map) -> (m2: cbor_map) -> (k: cbor) -> Lemma
  (ensures (cbor_map_get (cbor_map_union m1 m2) k == begin match cbor_map_get m1 k with
    | None -> cbor_map_get m2 k
    | v -> v
    end
  ))
  [SMTPat (cbor_map_get (cbor_map_union m1 m2) k)]

let cbor_map_set_keys_union (m1 m2: cbor_map) : Lemma
  (ensures (cbor_map_set_keys (cbor_map_union m1 m2) == (cbor_map_set_keys m1 `FS.union` cbor_map_set_keys m2)))
  [SMTPat (cbor_map_set_keys (cbor_map_union m1 m2))]
= assert (cbor_map_set_keys (cbor_map_union m1 m2) `FS.equal` (cbor_map_set_keys m1 `FS.union` cbor_map_set_keys m2))

let cbor_map_disjoint (m1 m2: cbor_map) : Tot prop =
  forall k . ~ (cbor_map_defined k m1 /\ cbor_map_defined k m2)

let cbor_map_length_disjoint_union (m1 m2: cbor_map) : Lemma
  (requires (cbor_map_disjoint m1 m2))
  (ensures (
    cbor_map_length (cbor_map_union m1 m2) == cbor_map_length m1 + cbor_map_length m2
  ))
= 
  assert (FS.intersection (cbor_map_set_keys m1) (cbor_map_set_keys m2) `FS.equal` FS.emptyset);
  assert (FS.cardinality (FS.union (cbor_map_set_keys m1) (cbor_map_set_keys m2)) == FS.cardinality (cbor_map_set_keys m1) + FS.cardinality (cbor_map_set_keys m2))

let cbor_map_mem (kv: (cbor & cbor)) (f: cbor_map) : Tot bool =
  cbor_map_get f (fst kv) = Some (snd kv)

let cbor_map_defined_alt
  (k: cbor) (f: cbor_map)
: Lemma
  (cbor_map_defined k f <==> (exists v . cbor_map_mem (k, v) f))
  [SMTPat (cbor_map_defined k f)]
= match cbor_map_get f k with
  | None -> ()
  | Some _ -> ()

let cbor_map_union_assoc (m1 m2 m3: cbor_map) : Lemma
  (cbor_map_union (cbor_map_union m1 m2) m3 == cbor_map_union m1 (cbor_map_union m2 m3))
= cbor_map_ext
    (cbor_map_union (cbor_map_union m1 m2) m3)
    (cbor_map_union m1 (cbor_map_union m2 m3))

let cbor_map_union_empty_l (m: cbor_map) : Lemma
  (cbor_map_union cbor_map_empty m == m)
  [SMTPat (cbor_map_union cbor_map_empty m)]
= cbor_map_ext (cbor_map_union cbor_map_empty m) m

let cbor_map_union_empty_r (m: cbor_map) : Lemma
  (cbor_map_union m cbor_map_empty == m)
  [SMTPat (cbor_map_union m cbor_map_empty)]
= cbor_map_ext (cbor_map_union m cbor_map_empty) m

let cbor_map_disjoint_mem_union (m1 m2: cbor_map) (xv: (cbor & cbor)) : Lemma
  (requires cbor_map_disjoint m1 m2)
  (ensures cbor_map_mem xv (m1 `cbor_map_union` m2) <==> cbor_map_mem xv m1 \/ cbor_map_mem xv m2)
= ()

let cbor_map_disjoint_mem_union' (m1 m2: cbor_map) (_: squash (cbor_map_disjoint m1 m2)) : Lemma
  (ensures forall xv . cbor_map_mem xv (m1 `cbor_map_union` m2) <==> cbor_map_mem xv m1 \/ cbor_map_mem xv m2)
= ()

let cbor_map_disjoint_union_comm (m1 m2: cbor_map) : Lemma
  (requires cbor_map_disjoint m1 m2)
  (ensures m1 `cbor_map_union` m2 == m2 `cbor_map_union` m1)
  [SMTPat (m1 `cbor_map_union` m2)]
= cbor_map_disjoint_mem_union' m1 m2 ();
  cbor_map_disjoint_mem_union' m2 m1 ();
  cbor_map_ext (m1 `cbor_map_union` m2) (m2 `cbor_map_union` m1)

let cbor_map_mem_filter
  (f: (cbor & cbor) -> Tot bool)
  (m: cbor_map)
  (x: (cbor & cbor))
: Lemma
  (cbor_map_mem x (cbor_map_filter f m) <==> cbor_map_mem x m /\ f x)
  [SMTPat (cbor_map_mem x (cbor_map_filter f m))]
= ()

let cbor_map_filter_for_all
  (f: (cbor & cbor) -> Tot bool)
  (m: cbor_map)
: Lemma
  (requires forall x . cbor_map_mem x m ==> f x)
  (ensures cbor_map_filter f m == m)
= cbor_map_ext (cbor_map_filter f m) m

let cbor_map_filter_for_all'
  (f: (cbor & cbor) -> Tot bool)
  (m: cbor_map)
  (sq: squash (forall x . cbor_map_mem x m ==> f x))
: Lemma
  (ensures cbor_map_filter f m == m)
= cbor_map_filter_for_all f m

let cbor_map_filter_ext
  (f1 f2: (cbor & cbor) -> Tot bool)
  (m: cbor_map)
: Lemma
  (requires forall x . f1 x == f2 x)
  (ensures cbor_map_filter f1 m == cbor_map_filter f2 m)
= cbor_map_ext (cbor_map_filter f1 m) (cbor_map_filter f2 m)

let cbor_map_disjoint_union_filter
  (f: (cbor & cbor) -> Tot bool)
  (m1 m2: cbor_map)
: Lemma
  (requires cbor_map_disjoint m1 m2)
  (ensures (cbor_map_filter f (cbor_map_union m1 m2) == cbor_map_filter f m1 `cbor_map_union` cbor_map_filter f m2))
= cbor_map_ext
    (cbor_map_filter f (cbor_map_union m1 m2))
    (cbor_map_filter f m1 `cbor_map_union` cbor_map_filter f m2)

let cbor_map_disjoint_union_filter'
  (f: (cbor & cbor) -> Tot bool)
  (m1 m2: cbor_map)
  (sq: squash (cbor_map_disjoint m1 m2))
: Lemma
  (ensures (cbor_map_filter f (cbor_map_union m1 m2) == cbor_map_filter f m1 `cbor_map_union` cbor_map_filter f m2))
= cbor_map_disjoint_union_filter f m1 m2

let cbor_map_filter_filter
  (p1 p2: (cbor & cbor) -> Tot bool)
  (f: cbor_map)
: Lemma
  (cbor_map_filter p2 (cbor_map_filter p1 f) == cbor_map_filter (p1 `U.andp` p2) f)
= cbor_map_ext
    (cbor_map_filter p2 (cbor_map_filter p1 f))
    (cbor_map_filter (p1 `U.andp` p2) f)

let cbor_map_filter_implies
  (p1 p2: (cbor & cbor) -> Tot bool)
  (f: cbor_map)
: Lemma
  (requires (forall kv . p1 kv ==> p2 kv))
  (ensures (cbor_map_filter p2 (cbor_map_filter p1 f) == cbor_map_filter p1 f))
= cbor_map_filter_filter p1 p2 f;
  cbor_map_filter_ext p1 (p1 `U.andp` p2) f

let cbor_map_split
  (f: (cbor & cbor) -> Tot bool)
  (m: cbor_map)
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

let cbor_map_equal' (f1 f2: cbor_map) : Tot prop
= forall kv . cbor_map_mem kv f1 <==> cbor_map_mem kv f2

let cbor_map_equiv (f1 f2: cbor_map) : Lemma
  (requires cbor_map_equal' f1 f2)
  (ensures f1 == f2)
  [SMTPat (cbor_map_equal' f1 f2)]
= let prf
    (k: cbor)
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
  (g g1 g2: cbor_map)
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
  (g1 g2 g: cbor_map)
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
  (m1 m2: cbor_map)
: Tot prop
= forall x . cbor_map_mem x m1 ==> cbor_map_mem x m2

let cbor_map_sub
  (m1 m2: cbor_map)
: Pure (cbor_map)
    (requires cbor_map_included m2 m1)
    (ensures fun m3 ->
      m2 `cbor_map_disjoint` m3 /\
      m2 `cbor_map_union` m3 == m1
    )
= let phi (kv: (cbor & cbor)) : Tot bool = not (cbor_map_mem kv m2) in
  let m3 = cbor_map_filter phi m1 in
  assert (cbor_map_disjoint m2 m3);
  cbor_map_disjoint_mem_union' m2 m3 ();
  cbor_map_equiv (cbor_map_union m2 m3) m1;
  m3

val cbor_map_key_list (m: cbor_map) : GTot (list cbor)

val cbor_map_key_list_mem (m: cbor_map) (k: cbor) : Lemma
  (ensures (List.Tot.memP k (cbor_map_key_list m) <==> cbor_map_defined k m))
  [SMTPat (List.Tot.memP k (cbor_map_key_list m))]

val cbor_map_key_list_no_repeats_p (m: cbor_map) : Lemma
  (ensures (List.Tot.no_repeats_p (cbor_map_key_list m)))
  [SMTPat (cbor_map_key_list m)]

val cbor_map_key_list_length (m: cbor_map) : Lemma
  (ensures (List.Tot.length (cbor_map_key_list m) == cbor_map_length m))
  [SMTPat (List.Tot.length (cbor_map_key_list m))]

let cbor_map_length_empty_equiv
  (m: cbor_map)
: Lemma
  (cbor_map_length m == 0 <==> m == cbor_map_empty)
= cbor_map_key_list_length m;
  match cbor_map_key_list m with
  | [] -> cbor_map_equiv m cbor_map_empty
  | a :: q -> cbor_map_key_list_mem m a

let cbor_map_disjoint_tot
  (m1 m2: cbor_map)
: Pure bool
    (requires True)
    (ensures fun b -> b <==> cbor_map_disjoint m1 m2)
= let f (xy: (cbor & cbor)) : Tot bool = cbor_map_defined (fst xy) m2 in
  let m1' = cbor_map_filter f m1 in
  cbor_map_key_list_length m1';
  assert (Nil? (cbor_map_key_list m1') ==> cbor_map_equal m1' cbor_map_empty);
  m1' = cbor_map_empty

val cbor_map_fold
  (#a: Type)
  (f: a -> cbor -> a)
  (x: a)
  (m: cbor_map)
: Tot a

val cbor_map_fold_ext
  (#a: Type)
  (f1 f2: a -> cbor -> a)
  (x: a)
  (m1 m2: cbor_map)
: Lemma
  (requires (
    (forall (x: a) (y: cbor) . cbor_map_defined y m1 ==> f1 x y == f2 x y) /\
    (forall (x: cbor) . cbor_map_defined x m1 <==> cbor_map_defined x m2)
  ))
  (ensures (cbor_map_fold f1 x m1 == cbor_map_fold f2 x m2))

val cbor_map_fold_eq
  (#a: Type)
  (f: a -> cbor -> a)
  (x: a)
  (m: cbor_map)
  (l: list cbor)
: Lemma
  (requires (
    U.op_comm f /\
    (forall (x: cbor) . List.Tot.memP x l <==> cbor_map_defined x m) /\
    List.Tot.no_repeats_p l
  ))
  (ensures (
    cbor_map_fold f x m == List.Tot.fold_left f x l
  ))

val cbor_map_fold_eq_idem
  (#a: Type)
  (f: a -> cbor -> a)
  (x: a)
  (m: cbor_map)
  (l: list cbor)
: Lemma
  (requires (
    U.op_comm f /\
    U.op_idem f /\
    (forall (x: cbor) . List.Tot.memP x l <==> cbor_map_defined x m)
  ))
  (ensures (
    cbor_map_fold f x m == List.Tot.fold_left f x l
  ))

let cbor_map_fold_empty
  (#a: Type)
  (f: a -> cbor -> a {
    U.op_comm f
  })
  (x: a)
: Lemma
  (cbor_map_fold f x cbor_map_empty == x)
= cbor_map_fold_eq f x cbor_map_empty []

let cbor_map_fold_singleton
  (#a: Type)
  (f: a -> cbor -> a {
    U.op_comm f
  })
  (x: a)
  (key value: cbor)
: Lemma
  (cbor_map_fold f x (cbor_map_singleton key value) == f x key)
= cbor_map_fold_eq f x (cbor_map_singleton key value) [key]

let cbor_map_fold_union
  (#a: Type)
  (f: a -> cbor -> a {
    U.op_comm f
  })
  (x: a)
  (m1 m2: cbor_map)
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

let cbor_map_ind_bounded
  (m: cbor_map)
  (p: (
    (m': cbor_map {
      cbor_map_included m' m
    }) -> prop
  ))
  (p0: squash (p cbor_map_empty))
  (ps: (
    (m': cbor_map {
      cbor_map_included m' m /\
      p m'
    }) ->
    (x: cbor {
      cbor_map_defined x m /\
      ~ (cbor_map_defined x m')
    }) ->
    Lemma
    (p (cbor_map_union m' (cbor_map_singleton x (Some?.v (cbor_map_get m x)))))
  ))
  (m': cbor_map {
    cbor_map_included m' m
  })
: Lemma
  (ensures p m')
= let l = cbor_map_key_list m' in
  let rec aux
    (l1: list cbor)
    (l2: list cbor {
      l == List.Tot.append l1 l2
    })
    (m1: cbor_map {
      cbor_map_included m1 m' /\
      (forall x . cbor_map_defined x m1 <==> List.Tot.memP x l1) /\
      p m1
    })
  : Lemma
    (ensures p m')
    (decreases l2)
  = match l2 with
    | [] ->
      List.Tot.append_l_nil l1;
      assert (cbor_map_equal m1 m')
    | a :: q ->
      List.Tot.append_assoc l1 [a] q;
      List.Tot.append_memP_forall l1 l2;
      List.Tot.append_memP_forall l1 [a];
      List.Tot.no_repeats_p_append l1 l2;
      ps m1 a;
      aux (List.Tot.append l1 [a]) q (cbor_map_union m1 (cbor_map_singleton a (Some?.v (cbor_map_get m' a))))
  in
  aux [] l cbor_map_empty

let cbor_map_ind
  (p: (cbor_map -> prop))
  (p0: squash (p cbor_map_empty))
  (ps: (
    (m': cbor_map {
      p m'
    }) ->
    (x: cbor {
      ~ (cbor_map_defined x m')
    }) ->
    (y: cbor) ->
    Lemma
    (p (cbor_map_union m' (cbor_map_singleton x y)))
  ))
  (m: cbor_map)
: Lemma
  (ensures p m)
= cbor_map_ind_bounded
    m
    p
    p0
    (fun m' x -> ps m' x (Some?.v (cbor_map_get m x)))
    m

let cbor_map_singleton_elim
  (s: cbor_map)
: Pure (cbor & cbor)
    (requires cbor_map_length s == 1)
    (ensures fun x -> cbor_map_equal s (cbor_map_singleton (fst x) (snd x)))
= let l = Ghost.hide (cbor_map_key_list s) in
  assert (forall x . List.Tot.memP x l <==> cbor_map_defined x s);
  assert (List.Tot.length l == 1);
  assert (forall x . cbor_map_defined x s <==> x == List.Tot.hd l);
  let t = (x: cbor { cbor_map_defined x s }) in
  let f (accu: option t) (x: cbor) : Tot (option t) =
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

type cbor_case =
  | CSimple: (v: simple_value) -> cbor_case
  | CInt64: (typ: major_type_uint64_or_neg_int64) -> (v: U64.t) -> cbor_case
  | CString: (typ: major_type_byte_string_or_text_string) -> (v: Seq.seq U8.t { FStar.UInt.fits (Seq.length v) U64.n /\ (typ == cbor_major_type_text_string ==> CBOR.Spec.API.UTF8.correct v) }) -> cbor_case
  | CArray: (v: list cbor { FStar.UInt.fits (List.Tot.length v) U64.n }) -> cbor_case
  | CMap: (c: cbor_map { FStar.UInt.fits (cbor_map_length c) U64.n }) -> cbor_case
  | CTagged: (tag: U64.t) -> (v: cbor) -> cbor_case

val unpack: cbor -> cbor_case

val pack: cbor_case -> cbor

val unpack_pack: (c: cbor_case) -> Lemma
  (ensures (unpack (pack c) == c))
  [SMTPat (pack c)]

val pack_unpack: (c: cbor) -> Lemma
  (ensures (pack (unpack c) == c))
  [SMTPat (unpack c)]

val unpack_precedes
  (c: cbor)
: Lemma
  (ensures (match unpack c with
  | CArray v -> (forall x . List.Tot.memP x v ==> x << c) // (v << c DOES NOT hold because of casting between the refinement on the list and the refinement on all its elements)
  | CMap v -> v << c
  | CTagged _ v -> v << c
  | _ -> True
  ))
  [SMTPat (unpack c)]

val cbor_map_depth : cbor -> Tot nat

val cbor_map_key_depth : cbor -> Tot nat
