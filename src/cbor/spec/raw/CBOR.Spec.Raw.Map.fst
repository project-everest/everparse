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

module CBOR.Spec.Raw.Map
include CBOR.Spec.Raw.Valid
open CBOR.Spec.Util

let rec list_sorted_map_entry_order_lt_tail
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool {
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z)
  })
  (a: (t1 & t2))
  (l: list (t1 & t2))
  (k: t1)
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) (a :: l) /\ List.Tot.memP k (List.Tot.map fst l)))
  (ensures (key_order (fst a) k))
  (decreases l)
= let b :: q = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (k == fst b)
  then ()
  else list_sorted_map_entry_order_lt_tail key_order b q k

let list_sorted_map_entry_order_not_memP_tail
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool {
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z)
  })
  (a: (t1 & t2))
  (l: list (t1 & t2))
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) (a :: l)))
  (ensures (~ (List.Tot.memP (fst a) (List.Tot.map fst l))))
= Classical.move_requires (list_sorted_map_entry_order_lt_tail key_order a l) (fst a)

let rec list_sorted_map_entry_order_no_repeats
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool {
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z)
  })
  (l: list (t1 & t2))
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) l))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l)))
= match l with
  | [] -> ()
  | a :: q ->
    list_sorted_map_entry_order_no_repeats key_order q;
    list_sorted_map_entry_order_not_memP_tail key_order a q

let list_sorted_map_assoc_ext
  (#t: eqtype)
  (#t': Type)
  (order: t -> t -> bool {
    order_irrefl order /\
    order_trans order
  })
  (l1 l2: list (t & t'))
: Lemma
  (requires (
    List.Tot.sorted (map_entry_order order _) l1 == true /\
    List.Tot.sorted (map_entry_order order _) l2 == true /\
    (forall x . List.Tot.assoc x l1 == List.Tot.assoc x l2)
  ))
  (ensures (
    l1 == l2
  ))
= list_sorted_map_entry_order_no_repeats order l1;
  list_sorted_map_entry_order_no_repeats order l2;
  list_assoc_no_repeats_equiv_recip l1 l2;
  list_sorted_ext_eq (map_entry_order order _) l1 l2

val list_sortWith: ('a -> 'a -> Tot bool) -> l:list 'a -> Tot (list 'a) (decreases (List.Tot.length l))
let rec list_sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo = List.Tot.partition (f pivot) tl in
     List.Tot.partition_length (f pivot) tl;
     List.Tot.append (list_sortWith f lo) (pivot::list_sortWith f hi)

let rec list_sortWith_length 
  (#a: Type)
  (f: a -> a -> bool)
  (l: list a)
: Lemma
  (ensures (List.Tot.length (list_sortWith f l) == List.Tot.length l))
  (decreases (List.Tot.length l))
= match l with
  | [] -> ()
  | pivot :: tl ->
    List.Tot.partition_length (f pivot) tl;
    let (hi, lo) = List.Tot.partition (f pivot) tl in
    list_sortWith_length f hi;
    list_sortWith_length f lo;
    List.Tot.append_length (list_sortWith f lo) (pivot :: list_sortWith f hi)

let rec list_sortWith_permutation (#a: eqtype) (f: a -> a -> bool) (l: list a) :
  Lemma (ensures forall x. List.Tot.count x l = List.Tot.count x (list_sortWith f l))
        (decreases List.Tot.length l)
= match l with
    | [] -> ()
    | pivot::tl ->
       let hi, lo  = List.Tot.partition (f pivot) tl in
       List.Tot.partition_length (f pivot) tl;
       List.Tot.partition_count_forall (f pivot) tl;
       list_sortWith_permutation f lo;
       list_sortWith_permutation f hi;
       List.Tot.append_count_forall (list_sortWith f lo) (pivot::list_sortWith f hi)

(** Correctness of the merging of two sorted lists around a pivot. *)
let rec list_append_sorted (#a:Type)
               (f:(a -> a -> Tot bool))
               (l1:list a{List.Tot.sorted f l1})
               (l2:list a{List.Tot.sorted f l2})
               (pivot:a)
:  Lemma (requires  (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)
                                    /\ (forall y. List.Tot.memP y l1 ==> f y pivot)
                                    /\ (forall y. List.Tot.memP y l2 ==> f pivot y)
                        )
                        (ensures (List.Tot.sorted f (List.Tot.append l1 (pivot::l2))))
                        (decreases l1)
                        [SMTPat (List.Tot.sorted f (List.Tot.append l1 (pivot::l2)))]
= match l1 with
  | [] -> ()
  | hd::tl -> list_append_sorted f tl l2 pivot


let rec list_partition_memP_forall (#a:Type) (f:(a -> Tot bool))
                  (l:list a)
                  : Lemma (requires True)
                          (ensures (let l1, l2 = List.Tot.partition f l in
                                    (forall x. List.Tot.memP x l <==> (List.Tot.memP x l1 \/ List.Tot.memP x l2))))
= match l with
  | [] -> ()
  | hd::tl -> list_partition_memP_forall f tl

let rec list_partition_memP_p_forall (#a:Type) (p:(a -> Tot bool))
                  (l:list a)
                  : Lemma (requires True)
                          (ensures (let l1, l2 = List.Tot.partition p l in
                                    (forall x. List.Tot.memP x l1 ==> p x) /\ (forall x. List.Tot.memP x l2 ==> not (p x))))
= match l with
  | [] -> ()
  | hd::tl -> list_partition_memP_p_forall p tl

let rec total_order_on_list
  (#t: Type)
  (f: (t -> t -> bool))
  (l: list t)
: Tot prop
= match l with
  | [] -> True
  | a :: q -> (forall (b: t) . List.Tot.memP b q ==> (f a b \/ f b a)) /\
    total_order_on_list f q

let rec partition_total_order_on_list
  (#t: Type)
  (f: (t -> t -> bool))
  (p: (t -> bool))
  (l: list t)
: Lemma
  (requires (total_order_on_list f l))
  (ensures (let (l1, l2) = List.Tot.partition p l in
    total_order_on_list f l1 /\ total_order_on_list f l2
  ))
= match l with
  | [] -> ()
  | a :: q ->
    partition_total_order_on_list f p q;
    list_partition_memP_forall p q

let list_sorted_memP_implies
  (#t: Type)
  (order: (t -> t -> bool) {
    order_trans order
  })
  (a: t)
  (l: list t)
  (x: t)
: Lemma
  ((
    List.Tot.sorted order (a :: l) /\
    List.Tot.memP x l
  ) ==>
  (order a x == true))
= Classical.move_requires (list_sorted_memP order a l) x

let rec sorted_total_order_on_list
  (#t: Type)
  (f: (t -> t -> bool))
  (l: list t)
: Lemma
  (requires (
    order_trans f /\
    List.Tot.sorted f l
  ))
  (ensures (
    total_order_on_list f l
  ))
= match l with
  | [] -> ()
  | [_] -> ()
  | a :: b :: q ->
    Classical.forall_intro (list_sorted_memP_implies f a (b :: q));
    sorted_total_order_on_list f (b :: q)

(** Correctness of [sortWith], part 2/2: the elements of [sortWith f
l] are sorted according to comparison function [f], and the elements
of [sortWith f l] are the elements of [l]. *)
let rec list_sortWith_sorted (#a:Type) (f:(a -> a -> Tot bool)) (l:list a) :
  Lemma (requires (total_order_on_list #a f l /\
    order_trans f /\
    (forall x y . ~ (f x y /\ f y x))
  ))
        (ensures ((List.Tot.sorted f (list_sortWith f l)) /\ (forall x. List.Tot.memP x l <==> List.Tot.memP x (list_sortWith f l))))
        (decreases List.Tot.length l)
=
  match l with
  | [] -> ()
  | pivot::tl ->
     let hi, lo  = List.Tot.partition (f pivot) tl in
     List.Tot.partition_length (f pivot) tl;
     list_partition_memP_forall (f pivot) tl;
     list_partition_memP_p_forall (f pivot) tl;
     partition_total_order_on_list f (f pivot) tl;
     list_sortWith_sorted f lo;
     list_sortWith_sorted f hi;
     List.Tot.append_memP_forall (list_sortWith f lo) (pivot::list_sortWith f hi);
     list_append_sorted f (list_sortWith f lo) (list_sortWith f hi) pivot

[@@noextract_to "krml"] noextract
let map_sort
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool)
  (l: list (t1 & t2))
: Tot (list (t1 & t2))
  (decreases (List.Tot.length l))
= list_sortWith (map_entry_order key_order _) l

let no_repeats_append_false_intro
  (#t: Type)
  (l1 l2: list t)
  (x: t)
: Lemma
  (requires (List.Tot.memP x l1 /\
    List.Tot.memP x l2
  ))
  (ensures (~ (List.Tot.no_repeats_p (List.Tot.append l1 l2))))
= Classical.move_requires (List.Tot.no_repeats_p_append_elim l1) l2

let rec no_repeats_fst_total_order_on_list
  (#t1: Type)
  (#t2: Type)
  (key_order: t1 -> t1 -> bool)
  (key_compare: t1 -> t1 -> int)
  (l: list (t1 & t2))
: Lemma
  (requires (
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z) /\
    (forall x y . key_order x y == (key_compare x y < 0)) /\
    (forall x y . key_compare x y == 0 <==> x == y) /\
    (forall x y . (key_compare x y < 0 <==> key_compare y x > 0))
  ))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l) <==> total_order_on_list (map_entry_order key_order _) l))
= match l with
  | [] -> ()
  | a :: q ->
    list_memP_map_forall fst q;
    no_repeats_fst_total_order_on_list key_order key_compare q

#restart-solver
let map_sort_correct
  (#t1: eqtype) // for assoc
  (#t2: Type)
  (key_order: t1 -> t1 -> bool)
  (key_compare: t1 -> t1 -> int)
  (l: list (t1 & t2))
: Lemma
  (requires (
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z) /\
    (forall x y . key_order x y == (key_compare x y < 0)) /\
    (forall x y . key_compare x y == 0 <==> x == y) /\
    (forall x y . (key_compare x y < 0 <==> key_compare y x > 0)) /\
    List.Tot.no_repeats_p (List.Tot.map fst l)
  ))
  (ensures (let l' = map_sort key_order l in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l')) /\
    List.Tot.sorted (map_entry_order key_order _) l' /\
    (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
  ))
= list_sortWith_length (map_entry_order key_order _) l;
  no_repeats_fst_total_order_on_list key_order key_compare l;
  list_sortWith_sorted (map_entry_order key_order _) l;
  let l' = map_sort key_order l in
  list_sorted_map_entry_order_no_repeats key_order l';
  list_assoc_no_repeats_equiv l l';
  ()

(* Map insertion *)

let map_entry_compare compare
  (x1 x2: raw_data_item & raw_data_item)
: Tot int
= compare (fst x1) (fst x2)

let rec map_insert
  compare
  (m: list (raw_data_item & raw_data_item))
  (kv: (raw_data_item & raw_data_item))
: Tot (option (list (raw_data_item & raw_data_item)))
= match m with
  | [] -> Some [kv]
  | kv' :: q ->
    let c = map_entry_compare compare kv' kv in
    if c < 0
    then begin
      match map_insert compare q kv with
      | None -> None
      | Some l' -> Some (kv' :: l')
    end
    else if c > 0
    then begin
      Some (kv :: m)
    end
    else None

let rec map_insert_mem
  compare
  (m: list (raw_data_item & raw_data_item))
  (kv: (raw_data_item & raw_data_item))
  (x: (raw_data_item & raw_data_item))
: Lemma
  (ensures (match map_insert compare m kv with
  | None -> True
  | Some l' -> List.Tot.memP x l' <==> List.Tot.memP x (kv :: m)
  ))
  (decreases m)
= match m with
  | [] -> ()
  | kv' :: q ->
    let c = map_entry_compare compare kv' kv in
    if c < 0
    then map_insert_mem compare q kv x
    else ()

let rec map_insert_sorted'
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    (forall x . order x x == false) /\
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    (forall x y . order x y == (compare x y < 0)) /\
    (forall x y . compare x y == 0 <==> x == y) /\
    (forall x y . (compare x y < 0 <==> compare y x > 0))
  })
  (m: list (raw_data_item & raw_data_item))
  (kv: (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.sorted (map_entry_order order _) m
  ))
  (ensures (
    let ol' = map_insert compare m kv in
    (None? ol' <==> List.Tot.memP (fst kv) (List.Tot.map fst m)) /\
    begin match ol' with
    | None -> True
    | Some l' -> List.Tot.sorted (map_entry_order order _) l'
    end
  ))
  (decreases m)
= match m with
  | [] -> ()
  | kv' :: q ->
    let c = map_entry_compare compare kv' kv in
    if c < 0
    then begin
      map_insert_sorted' order compare q kv;
      ()
    end
    else if c > 0
    then begin
      assert (map_entry_order order _ kv kv');
      CBOR.Spec.Raw.Map.list_sorted_map_entry_order_not_memP_tail order kv m;
      ()
    end
    else ()

let map_insert_sorted
  (order: raw_data_item -> raw_data_item -> bool)
  (compare: raw_data_item -> raw_data_item -> int {
    
    (forall x . order x x == false) /\
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    (forall x y . order x y == (compare x y < 0)) /\
    (forall x y . compare x y == 0 <==> x == y) /\
    (forall x y . (compare x y < 0 <==> compare y x > 0))
  })
  (m: list (raw_data_item & raw_data_item))
  (kv: (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.sorted (map_entry_order order _) m
  ))
  (ensures (
    let ol' = map_insert compare m kv in
    (None? ol' <==> List.Tot.memP (fst kv) (List.Tot.map fst m)) /\
    begin match ol' with
    | None -> True
    | Some l' -> List.Tot.sorted (map_entry_order order _) l'
    end
  ))
= map_insert_sorted' order compare m kv
