module CBOR.Spec.Raw.DupCheck
include CBOR.Spec.Raw.Canonical
open CBOR.Spec.Util

(* Specification of a map key duplicate check for raw CBOR data items
   that are well-formed but not necessarily valid. Map keys are
   compared with the canonical order `cc`, which coincides with the
   basic data model equivalence on valid items. The traversal mirrors
   `CBOR.Spec.Raw.Nondet.check_map_depth`: inner maps (including maps
   in keys) are checked before the keys of the enclosing map are
   compared. *)

let cc_eq0 (a b: raw_data_item) : Tot bool = cc a b = 0

let no_cc_dup (l: list raw_data_item) : Tot bool =
  list_no_setoid_repeats cc_eq0 l

let rec check_dups
  (l: list raw_data_item)
: Tot bool
  (decreases (list_sum raw_data_item_size l))
= match l with
  | [] -> true
  | a :: q ->
    raw_data_item_size_eq a;
    match a with
    | Tagged _ v -> check_dups (v :: q)
    | Array _ v ->
      list_sum_append raw_data_item_size v q;
      check_dups (List.Tot.append v q)
    | Map _ v ->
      list_of_pair_list_sum raw_data_item_size v;
      check_dups (list_of_pair_list v) &&
      no_cc_dup (List.Tot.map fst v) &&
      check_dups q
    | _ -> check_dups q

let no_cc_dup_correct
  (l: list raw_data_item)
: Lemma
  (requires List.Tot.for_all valid_raw_data_item l)
  (ensures no_cc_dup l == list_no_setoid_repeats raw_equiv l)
= list_no_setoid_repeats_ext cc_eq0 raw_equiv l (fun l1 l2 x y ->
    List.Tot.for_all_mem valid_raw_data_item l;
    List.Tot.append_memP l1 l2 x;
    List.Tot.append_memP l1 l2 y;
    cc_equiv x y
  )

let rec check_dups_correct
  (l: list raw_data_item)
: Lemma
  (ensures check_dups l == List.Tot.for_all valid_raw_data_item l)
  (decreases (list_sum raw_data_item_size l))
= match l with
  | [] -> ()
  | a :: q ->
    raw_data_item_size_eq a;
    valid_eq basic_data_model a;
    match a with
    | Tagged _ v -> check_dups_correct (v :: q)
    | Array _ v ->
      list_sum_append raw_data_item_size v q;
      List.Tot.for_all_append valid_raw_data_item v q;
      check_dups_correct (List.Tot.append v q)
    | Map _ v ->
      list_of_pair_list_sum raw_data_item_size v;
      check_dups_correct (list_of_pair_list v);
      list_of_pair_list_for_all valid_raw_data_item v;
      list_of_pair_list_map valid_raw_data_item v;
      if List.Tot.for_all valid_raw_data_item (List.Tot.map fst v)
      then no_cc_dup_correct (List.Tot.map fst v);
      check_dups_correct q
    | _ -> check_dups_correct q

let check_dups_valid
  (x: raw_data_item)
: Lemma
  (check_dups [x] == valid_raw_data_item x)
= check_dups_correct [x]

let rec list_existsb_index (#t: Type) (p: t -> bool) (l: list t) : Lemma
  (List.Tot.existsb p l == true <==> (exists (k: nat) . k < List.Tot.length l /\ p (List.Tot.index l k) == true))
= match l with
  | [] -> ()
  | a :: q ->
    list_existsb_index p q;
    let prf (k: nat) : Lemma
      (requires k < List.Tot.length l /\ p (List.Tot.index l k) == true)
      (ensures List.Tot.existsb p l == true)
    = if k = 0 then () else assert (p (List.Tot.index q (k - 1)) == true)
    in
    Classical.forall_intro (Classical.move_requires prf);
    if p a then assert (List.Tot.index l 0 == a)
    else if List.Tot.existsb p q then begin
      let prf' (k: nat) : Lemma
        (requires k < List.Tot.length q /\ p (List.Tot.index q k) == true)
        (ensures exists (k': nat) . k' < List.Tot.length l /\ p (List.Tot.index l k') == true)
      = assert (List.Tot.index l (k + 1) == List.Tot.index q k)
      in
      Classical.forall_intro (Classical.move_requires prf')
    end

let list_no_repeats_index (#t: Type) (eq: t -> t -> bool) (l: list t) : prop =
  forall (i j: nat) . (i < j /\ j < List.Tot.length l) ==> eq (List.Tot.index l i) (List.Tot.index l j) == false

let rec list_no_setoid_repeats_index (#t: Type) (eq: t -> t -> bool) (l: list t) : Lemma
  (list_no_setoid_repeats eq l == true <==> list_no_repeats_index eq l)
= match l with
  | [] -> ()
  | a :: q ->
    list_no_setoid_repeats_index eq q;
    list_existsb_index (eq a) q;
    let prf1 (i j: nat) : Lemma
      (requires list_no_setoid_repeats eq l == true /\ i < j /\ j < List.Tot.length l)
      (ensures (i < j /\ j < List.Tot.length l) ==> eq (List.Tot.index l i) (List.Tot.index l j) == false)
    = if i = 0
      then assert (eq a (List.Tot.index q (j - 1)) == false)
      else assert (eq (List.Tot.index q (i - 1)) (List.Tot.index q (j - 1)) == false)
    in
    let prf2 (k: nat) : Lemma
      (requires list_no_repeats_index eq l /\ k < List.Tot.length q)
      (ensures k < List.Tot.length q ==> eq a (List.Tot.index q k) == false)
    = assert (List.Tot.index l 0 == a);
      assert (List.Tot.index l (k + 1) == List.Tot.index q k)
    in
    let prf3 (i j: nat) : Lemma
      (requires list_no_repeats_index eq l /\ i < j /\ j < List.Tot.length q)
      (ensures (i < j /\ j < List.Tot.length q) ==> eq (List.Tot.index q i) (List.Tot.index q j) == false)
    = assert (List.Tot.index l (i + 1) == List.Tot.index q i);
      assert (List.Tot.index l (j + 1) == List.Tot.index q j)
    in
    Classical.forall_intro_2 (fun i -> Classical.move_requires (prf1 i));
    Classical.forall_intro (Classical.move_requires prf2);
    Classical.forall_intro_2 (fun i -> Classical.move_requires (prf3 i))

let no_cc_dup_index (l: list raw_data_item) : Lemma
  (no_cc_dup l == true <==> list_no_repeats_index cc_eq0 l)
= list_no_setoid_repeats_index cc_eq0 l
