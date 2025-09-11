module CBOR.Spec.Raw.NoMap

(*
let rec raw_equiv_list_no_map_append
  (ll1 lr1 ll2 lr2: list raw_data_item)
: Lemma
  (requires (List.Tot.length ll1 == List.Tot.length ll2))
  (ensures (raw_equiv_list_no_map (List.Tot.append ll1 lr1) (List.Tot.append ll2 lr2) == (raw_equiv_list_no_map ll1 ll2 && raw_equiv_list_no_map lr1 lr2)))
  (decreases (list_sum raw_data_item_size ll1))
= match ll1, ll2 with
  | x1 :: q1, x2 :: q2 ->
    raw_data_item_size_eq x1;
    begin match x1, x2 with
    | Tagged tag1 v1, Tagged tag2 v2 ->
      raw_equiv_list_no_map_append (v1 :: q1) lr1 (v2 :: q2) lr2
    | Array len1 v1, Array len2 v2 ->
      list_sum_append raw_data_item_size v1 q1;
      if raw_uint64_equiv len1 len2
      then begin
        assert (List.Tot.length v1 == List.Tot.length v2);
        List.Tot.append_assoc v1 q1 lr1;
        List.Tot.append_assoc v2 q2 lr2;
        List.Tot.append_length v1 q1;
        List.Tot.append_length v2 q2;
        raw_equiv_list_no_map_append (List.Tot.append v1 q1) lr1 (List.Tot.append v2 q2) lr2
      end
    | _ -> raw_equiv_list_no_map_append q1 lr1 q2 lr2
    end
  | _ -> ()

let rec raw_equiv_list_no_map_no_map
  (l1 l2: list raw_data_item)
: Lemma
  (requires (raw_equiv_list_no_map l1 l2 == true))
  (ensures (List.Tot.for_all (holds_on_raw_data_item (notp Map?)) l1 == true))
  (decreases (list_sum raw_data_item_size l1))
= match l1, l2 with
  | x1 :: q1, x2 :: q2 ->
    raw_data_item_size_eq x1;
    holds_on_raw_data_item_eq (notp Map?) x1;
    begin match x1, x2 with
    | Tagged _ v1, Tagged _ v2 ->
      raw_equiv_list_no_map_no_map (v1 :: q1) (v2 :: q2)
    | Array _ v1, Array _ v2 ->
      list_sum_append raw_data_item_size v1 q1;
      raw_equiv_list_no_map_no_map (v1 `List.Tot.append` q1) (v2 `List.Tot.append` q2);
      List.Tot.for_all_append (holds_on_raw_data_item (notp Map?)) v1 q1
    | _ -> raw_equiv_list_no_map_no_map q1 q2
    end
  | _ -> ()


let rec raw_equiv_list_no_map_equiv
  (l1 l2: list raw_data_item)
: Lemma
  (requires (raw_equiv_list_no_map l1 l2 == true))
  (ensures (list_for_all2 raw_equiv l1 l2 == true))
  (decreases (list_sum raw_data_item_size l1))
= match l1, l2 with
  | x1 :: q1, x2 :: q2 ->
    raw_data_item_size_eq x1;
    raw_equiv_eq x1 x2;
    holds_on_raw_data_item_eq (notp Map?) x1;
    begin match x1, x2 with
    | Tagged _ v1, Tagged _ v2 ->
      raw_equiv_list_no_map_equiv (v1 :: q1) (v2 :: q2)
    | Array _ v1, Array _ v2 ->
      list_sum_append raw_data_item_size v1 q1;
      raw_equiv_list_no_map_equiv (v1 `List.Tot.append` q1) (v2 `List.Tot.append` q2);
      list_for_all2_append raw_equiv v1 q1 v2 q2
    | _ -> raw_equiv_list_no_map_equiv q1 q2
    end
  | _ -> ()


let rec raw_equiv_list_no_map_sym'
  (l1 l2: list raw_data_item)
: Lemma
  (requires (raw_equiv_list_no_map l1 l2 == true))
  (ensures (raw_equiv_list_no_map l2 l1 == true))
  (decreases (list_sum raw_data_item_size l1))
= match l1, l2 with
  | x1 :: q1, x2 :: q2 ->
    raw_data_item_size_eq x1;
    raw_data_item_size_eq x2;
    begin match x1, x2 with
    | Array len1 v1, Array len2 v2 ->
      list_sum_append raw_data_item_size v1 q1;
      raw_equiv_list_no_map_sym' (v1 `List.Tot.append` q1) (v2 `List.Tot.append` q2)
    | Tagged tag1 v1, Tagged tag2 v2 ->
      raw_equiv_list_no_map_sym' (v1 :: q1) (v2 :: q2)
    | _ -> raw_equiv_list_no_map_sym' q1 q2
    end
  | _ -> ()

let raw_equiv_list_no_map_sym
  (l1 l2: list raw_data_item)
: Lemma
  (raw_equiv_list_no_map l1 l2 == raw_equiv_list_no_map l2 l1)
= Classical.move_requires (raw_equiv_list_no_map_sym' l1) l2;
  Classical.move_requires (raw_equiv_list_no_map_sym' l2) l1

let rec raw_equiv_equiv_list_no_map
  (l1 l2: list raw_data_item)
: Lemma
  (requires (
    list_for_all2 raw_equiv l1 l2 == true /\
    list_for_all2 (prod_or (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?))) l1 l2 == true
  ))
  (ensures (
    raw_equiv_list_no_map l1 l2 == true
  ))
  (decreases (list_sum raw_data_item_size l1))
= match l1, l2 with
  | x1 :: q1, x2 :: q2 ->
    raw_data_item_size_eq x1;
    raw_equiv_eq x1 x2;
    begin match x1, x2 with
    | Array len1 v1, Array len2 v2 ->
      list_sum_append raw_data_item_size v1 q1;
      list_for_all2_append raw_equiv v1 q1 v2 q2;
      list_for_all2_prod_or_weak (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?)) v1 v2;
      list_for_all2_append (prod_or (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?))) v1 q1 v2 q2;
      raw_equiv_equiv_list_no_map (v1 `List.Tot.append` q1) (v2 `List.Tot.append` q2)
    | Tagged tag1 v1, Tagged tag2 v2 ->
      raw_equiv_equiv_list_no_map (v1 :: q1) (v2 :: q2)
    | _ -> raw_equiv_equiv_list_no_map q1 q2
    end
  | _ -> ()

let raw_equiv_list_no_map_eq
  (l1 l2: list raw_data_item)
: Lemma
  (raw_equiv_list_no_map l1 l2 == (list_for_all2 raw_equiv l1 l2 && list_for_all2 (prod_or (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?))) l1 l2))
= if raw_equiv_list_no_map l1 l2
  then begin
    raw_equiv_list_no_map_no_map l1 l2;
    raw_equiv_list_no_map_equiv l1 l2;
    list_for_all2_length raw_equiv l1 l2;
    list_for_all2_prod_or_weak (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?)) l1 l2
  end
  else if (list_for_all2 raw_equiv l1 l2 && list_for_all2 (prod_or (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?))) l1 l2)
  then raw_equiv_equiv_list_no_map l1 l2
  else ()

let rec raw_equiv_list_no_map_eq'
  (l1 l2: list raw_data_item)
: Lemma
  (ensures (raw_equiv_list_no_map l1 l2 == list_for_all2 raw_equiv_no_map l1 l2))
  (decreases l1)
= raw_equiv_list_no_map_eq l1 l2;
  match l1, l2 with
  | a1 :: q1, a2 :: q2 ->
    raw_equiv_list_no_map_eq [a1] [a2];
    raw_equiv_list_no_map_eq q1 q2;
    raw_equiv_list_no_map_eq' q1 q2
  | _ -> ()

let valid_no_maps_in_keys_no_maps_in_keys_gen
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item_no_maps_in_keys_gen p x == true))
  (ensures (holds_on_raw_data_item p x == true))
= holds_on_raw_data_item_implies
    (valid_raw_data_item_no_maps_in_keys_elem_gen p)
    p
    (fun x' -> ())
    x

let rec valid_no_maps_in_keys_valid_map
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (holds_on_pair valid_raw_data_item_no_maps_in_keys) l == true /\
    no_maps_in_keys_map l == true /\
    valid_raw_data_item_no_maps_in_keys_map l == true
  ))
  (ensures (
    valid_raw_data_item_map l == true
  ))
= match l with
  | [] -> ()
  | a :: q ->
    valid_no_maps_in_keys_valid_map q;
    if List.Tot.existsb (map_entry_order raw_equiv _ a) q
    then begin
      let a' = list_existsb_elim (map_entry_order raw_equiv _ a) q in
      assert (List.Tot.memP a l);
      assert (List.Tot.memP a' l);
      List.Tot.for_all_mem (holds_on_pair valid_raw_data_item_no_maps_in_keys) l;
      List.Tot.memP_map_intro fst a l;
      List.Tot.memP_map_intro fst a' l;
      valid_no_maps_in_keys_no_maps_in_keys (fst a);
      valid_no_maps_in_keys_no_maps_in_keys (fst a');
      list_for_all2_prod_or_weak (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?)) [fst a] [fst a'];
      raw_equiv_equiv_list_no_map [fst a] [fst a'];
      list_existsb_intro (map_entry_order raw_equiv_no_map _ a) q a'
    end

let valid_no_maps_in_keys_valid
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item_no_maps_in_keys x == true))
  (ensures (valid_raw_data_item x == true))
= holds_on_raw_data_item_implies
    valid_raw_data_item_no_maps_in_keys_elem
    valid_raw_data_item_elem
    (fun x' -> 
      assert_norm (valid_raw_data_item_no_maps_in_keys == holds_on_raw_data_item valid_raw_data_item_no_maps_in_keys_elem);
      match x' with
      | Map len v ->
        holds_on_raw_data_item_eq_map valid_raw_data_item_no_maps_in_keys_elem len v;
        valid_no_maps_in_keys_valid_map v
      | _ -> ()
    )
    x

let valid_no_maps_in_keys_valid_gen
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (
    valid_raw_data_item_no_maps_in_keys_gen p x == true /\
    (forall x' . p x' == true ==> no_maps_in_keys_elem x' == true)
  ))
  (ensures (valid_raw_data_item x == true))
= holds_on_raw_data_item_implies
    (valid_raw_data_item_no_maps_in_keys_elem_gen p)
    valid_raw_data_item_no_maps_in_keys_elem
    (fun x' -> ())
    x;
  valid_no_maps_in_keys_valid x

let rec valid_valid_no_maps_in_keys_map
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    valid_raw_data_item_map l == true
  ))
  (ensures (
    valid_raw_data_item_no_maps_in_keys_map l == true
  ))
= match l with
  | [] -> ()
  | a :: q ->
    valid_valid_no_maps_in_keys_map q;
    if List.Tot.existsb (map_entry_order raw_equiv_no_map _ a) q
    then
      list_existsb_implies (map_entry_order raw_equiv_no_map _ a) (map_entry_order raw_equiv _ a) q (fun a' -> raw_equiv_list_no_map_equiv [fst a] [fst a'])

let valid_valid_no_maps_in_keys_gen
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item x == true /\
    holds_on_raw_data_item p x == true
  ))
  (ensures (valid_raw_data_item_no_maps_in_keys_gen p x == true))
= holds_on_raw_data_item_andp
    valid_raw_data_item_elem
    p
    x;
  holds_on_raw_data_item_implies
    (andp valid_raw_data_item_elem p)
    (valid_raw_data_item_no_maps_in_keys_elem_gen p)
    (fun x' -> 
      match x' with
      | Map len v ->
        holds_on_raw_data_item_eq_map valid_raw_data_item len v;
        valid_valid_no_maps_in_keys_map v
      | _ -> ()
    )
    x

let valid_valid_no_maps_in_keys
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item x == true /\
    no_maps_in_keys x == true
  ))
  (ensures (valid_raw_data_item_no_maps_in_keys x == true))
= assert_norm (valid_raw_data_item_no_maps_in_keys x == valid_raw_data_item_no_maps_in_keys_gen no_maps_in_keys_elem x);
  valid_valid_no_maps_in_keys_gen no_maps_in_keys_elem x

let valid_raw_data_item_no_maps_in_keys_eq
  (x: raw_data_item)
: Lemma
  (valid_raw_data_item_no_maps_in_keys x ==
    (valid_raw_data_item x && no_maps_in_keys x)
  )
= Classical.move_requires valid_no_maps_in_keys_no_maps_in_keys x;
  Classical.move_requires valid_no_maps_in_keys_valid x;
  Classical.move_requires valid_valid_no_maps_in_keys x

let valid_raw_data_item_no_maps_in_keys_gen_eq
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (
    forall x' . p x' == true ==> no_maps_in_keys_elem x' == true
  ))
  (ensures (valid_raw_data_item_no_maps_in_keys_gen p x ==
    (valid_raw_data_item x && holds_on_raw_data_item p x)
  ))
= Classical.move_requires (valid_no_maps_in_keys_no_maps_in_keys_gen p) x;
  Classical.move_requires (valid_no_maps_in_keys_valid_gen p) x;
  Classical.move_requires (valid_valid_no_maps_in_keys_gen p) x
