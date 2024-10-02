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

[@@noextract_to "krml"] noextract
let rec map_sort_merge
  (#t1 #t2: Type)
  (key_compare: t1 -> t1 -> int)
  (accu: list (t1 & t2))
  (l1: list (t1 & t2))
  (l2: list (t1 & t2))
: Tot (bool & list (t1 & t2))
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  |  (k1, v1) :: l1', (k2, v2) :: l2' ->
    begin let c = key_compare k1 k2 in
      if c = 0
      then (false, accu `List.Tot.append` (l1 `List.Tot.append` l2))
      else if c < 0
      then map_sort_merge key_compare (accu `List.Tot.append` [(k1, v1)]) l1' l2
      else
        map_sort_merge key_compare (accu `List.Tot.append` [(k2, v2)]) l1 l2'
        // TODO in this case:
        // 1. prove that the sort is stable, i.e. that the maps are extensionally equal throughout
        // 2. extract and swap the whole prefix of l2 less than the head of l1, rather than just the head of l2
     end
  | [], _ -> (true, accu `List.Tot.append` l2)
  | _, [] -> (true, accu `List.Tot.append` l1)

#push-options "--z3rlimit 16"

#restart-solver
let rec map_sort_merge_correct
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool)
  (key_compare: t1 -> t1 -> int)
  (accu: list (t1 & t2))
  (l1: list (t1 & t2))
  (l2: list (t1 & t2))
: Lemma
  (requires (
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z) /\
    (forall x y . key_order x y == (key_compare x y < 0)) /\
    (forall x y . key_compare x y == 0 <==> x == y) /\
    (forall x y . (key_compare x y < 0 <==> key_compare y x > 0)) /\
    List.Tot.sorted (map_entry_order key_order _) (accu `List.Tot.append` l1) /\
    List.Tot.sorted (map_entry_order key_order _) (accu `List.Tot.append` l2)
  ))
  (ensures (
    let (sorted, res) = map_sort_merge key_compare accu l1 l2 in
    List.Tot.length res == List.Tot.length accu + List.Tot.length l1 + List.Tot.length l2 /\
    (forall x . List.Tot.memP x res <==> List.Tot.memP x (accu `List.Tot.append` (l1 `List.Tot.append` l2))) /\
    (List.Tot.no_repeats_p (List.Tot.map fst res) <==> List.Tot.no_repeats_p (List.Tot.map fst (accu `List.Tot.append` (l1 `List.Tot.append` l2)))) /\
    (if sorted
    then List.Tot.sorted (map_entry_order key_order _) res
    else ~ (List.Tot.no_repeats_p (List.Tot.map fst res))
    )
  ))
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  | [], _ -> List.Tot.append_length accu l2
  | _, [] -> List.Tot.append_l_nil l1; List.Tot.append_length accu l1
  | (k1, v1) :: l1', (k2, v2) :: l2' ->
    List.Tot.map_append fst l1 l2;
    List.Tot.map_append fst accu (l1 `List.Tot.append` l2);
    let c = key_compare k1 k2 in
    if c = 0
    then
      List.Tot.no_repeats_p_false_intro (List.Tot.map fst accu) [k1] (List.Tot.map fst l1') (List.Tot.map fst l2')
    else if c < 0
    then begin
      let accu' = accu `List.Tot.append` [(k1, v1)] in
      List.Tot.append_length accu [(k1, v1)];
      List.Tot.append_assoc accu l1 l2;
      List.Tot.append_assoc accu [(k1, v1)] l1';
      List.Tot.append_assoc accu' l1' l2;
      List.Tot.append_assoc accu [(k1, v1)] l2;
      list_sorted_append_elim (map_entry_order key_order _) accu' l1';
      list_sorted_append_elim (map_entry_order key_order _) accu l2;
      list_sorted_append_chunk_intro (map_entry_order key_order _) accu [(k1, v1)] l2;
      map_sort_merge_correct key_order key_compare accu' l1' l2
    end
    else begin
      let accu' = accu `List.Tot.append` [(k2, v2)] in
      List.Tot.append_length accu [(k2, v2)];
      List.Tot.append_memP_forall l1 l2;
      List.Tot.append_memP_forall accu (l1 `List.Tot.append` l2);
      List.Tot.append_memP_forall accu [(k2, v2)];
      List.Tot.append_memP_forall l1 l2';
      List.Tot.append_memP_forall accu' (l1 `List.Tot.append` l2');
      List.Tot.no_repeats_p_append_permut (List.Tot.map fst accu) [k2] (List.Tot.map fst l1) [] (List.Tot.map fst l2');
      List.Tot.append_assoc (List.Tot.map fst accu) [k2] (List.Tot.map fst l1 `List.Tot.append` List.Tot.map fst l2');
      List.Tot.map_append fst accu [(k2, v2)];
      List.Tot.map_append fst l1 l2';
      List.Tot.map_append fst accu' (l1 `List.Tot.append` l2');
      List.Tot.append_assoc accu [(k2, v2)] l2';
      list_sorted_append_elim (map_entry_order key_order _) accu' l2';
      list_sorted_append_elim (map_entry_order key_order _) accu l1;
      list_sorted_append_chunk_intro (map_entry_order key_order _) accu [(k2, v2)] l1;
      List.Tot.append_assoc accu [(k2, v2)] l1;
      map_sort_merge_correct key_order key_compare accu' l1 l2'
    end

#pop-options

[@@noextract_to "krml"] noextract
let rec map_sort
  (#t1 #t2: Type)
  (key_compare: t1 -> t1 -> int)
  (l: list (t1 & t2))
: Tot (bool & list (t1 & t2))
  (decreases (List.Tot.length l))
= let len = List.Tot.length l in
  if len < 2
  then (true, l)
  else
    let (l1, l2) = List.Tot.splitAt (len / 2) l in
    let (res, l1') = map_sort key_compare l1 in
    if not res
    then (false, l1' `List.Tot.append` l2)
    else
      let (res, l2') = map_sort key_compare l2 in
      if not res
      then (false, l1' `List.Tot.append` l2')
      else map_sort_merge key_compare [] l1' l2'

#push-options "--z3rlimit 64"

#restart-solver
let rec map_sort_correct
  (#t1: eqtype)
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
  (ensures (let (res, l') = map_sort key_compare l in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l') <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (res == true <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (res == true ==> (
      List.Tot.sorted (map_entry_order key_order _) l' /\
      (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
    ))
  ))
  (decreases (List.Tot.length l))
= let len = List.Tot.length l in
  if len < 2
  then ()
  else begin
    let (l1, l2) = List.Tot.splitAt (len / 2) l in
    list_splitAt_append (len / 2) l;
    List.Tot.append_length l1 l2;
    List.Tot.append_memP_forall l1 l2;
    List.Tot.map_append fst l1 l2;
    List.Tot.no_repeats_p_append (List.Tot.map fst l1) (List.Tot.map fst l2);
    List.Tot.append_memP_forall (List.Tot.map fst l1) (List.Tot.map fst l2);
    list_memP_map_forall fst l1;
    list_memP_map_forall fst l2;
    let (res, l1') = map_sort key_compare l1 in
    map_sort_correct key_order key_compare l1;
    list_memP_map_forall fst l1';
    List.Tot.append_memP_forall (List.Tot.map fst l1') (List.Tot.map fst l2);
    List.Tot.no_repeats_p_append (List.Tot.map fst l1') (List.Tot.map fst l2);
    List.Tot.map_append fst l1' l2;
    List.Tot.append_memP_forall l1' l2;
    if not res
    then List.Tot.append_length l1' l2
    else begin
      let (res, l2') = map_sort key_compare l2 in
      map_sort_correct key_order key_compare l2;
      list_memP_map_forall fst l2';
      List.Tot.append_memP_forall (List.Tot.map fst l1') (List.Tot.map fst l2');
      List.Tot.no_repeats_p_append (List.Tot.map fst l1') (List.Tot.map fst l2');
      List.Tot.map_append fst l1' l2';
      List.Tot.append_memP_forall l1' l2';
      if not res
      then List.Tot.append_length l1' l2'
      else begin
        let (res, l') = map_sort_merge key_compare [] l1' l2' in
        assert (map_sort key_compare l == (res, l'));
        map_sort_merge_correct key_order key_compare [] l1' l2';
        assert (forall x . List.Tot.memP x l' <==> (List.Tot.memP x l1' \/ List.Tot.memP x l2'));
        assert (forall x . List.Tot.memP x l' <==> List.Tot.memP x l);
        assert (List.Tot.no_repeats_p (List.Tot.map fst l') <==> List.Tot.no_repeats_p (List.Tot.map fst l));
        if res
        then begin
          assert (List.Tot.sorted (map_entry_order key_order _) l');
          list_sorted_map_entry_order_no_repeats key_order l';
          list_assoc_no_repeats_equiv l l';
          assert (forall k . List.Tot.assoc k l' == List.Tot.assoc k l)
        end
        else ()
      end
    end
  end

  #pop-options
