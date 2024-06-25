module CBOR.Spec.Raw.Valid

let rec raw_equiv_sorted_optimal
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (x1 x2: raw_data_item)
: Lemma
  (requires (
    raw_equiv x1 x2 /\
    raw_data_item_sorted order x1 /\
    raw_data_item_sorted order x2 /\
    raw_data_item_ints_optimal x1 /\
    raw_data_item_ints_optimal x2
  ))
  (ensures (x1 == x2))
  (decreases x1)
= raw_equiv_eq x1 x2;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x1;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x2;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x1;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x2;
  match x1, x2 with
  | Simple _, Simple _ -> ()
  | Int64 _ v1, Int64 _ v2 ->
    raw_uint64_optimal_unique v1 v2
  | String _ v1 _, String _ v2 _ ->
    raw_uint64_optimal_unique v1 v2
  | Tagged tag1 v1, Tagged tag2 v2 ->
    raw_uint64_optimal_unique tag1 tag2;
    raw_equiv_sorted_optimal order v1 v2
  | Array len1 l1, Array len2 l2 ->
    raw_uint64_optimal_unique len1 len2;
    assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
    list_for_all2_prod (raw_data_item_sorted order) (raw_data_item_sorted order) l1 l2;
    list_for_all2_prod raw_data_item_ints_optimal raw_data_item_ints_optimal l1 l2;
    list_for_all2_andp_intro
      (prodp (raw_data_item_sorted order) (raw_data_item_sorted order))
      (prodp raw_data_item_ints_optimal raw_data_item_ints_optimal)
      l1 l2;
    list_for_all2_andp_intro
      (andp2
        (prodp (raw_data_item_sorted order) (raw_data_item_sorted order))
        (prodp raw_data_item_ints_optimal raw_data_item_ints_optimal))
      raw_equiv
      l1 l2;
    list_for_all2_implies
      (andp2
        (andp2
          (prodp (raw_data_item_sorted order) (raw_data_item_sorted order))
          (prodp raw_data_item_ints_optimal raw_data_item_ints_optimal))
        raw_equiv
      )
      ( = )
      l1 l2
      (fun x1' x2' ->
        raw_equiv_sorted_optimal order x1' x2'
      );
    list_for_all2_equals l1 l2
  | Map len1 l1, Map len2 l2 ->
    raw_uint64_optimal_unique len1 len2;
    assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
    list_for_all_andp (holds_on_pair (raw_data_item_sorted order)) (holds_on_pair raw_data_item_ints_optimal) l1;
    list_for_all_andp (holds_on_pair (raw_data_item_sorted order)) (holds_on_pair raw_data_item_ints_optimal) l2;
    list_for_all_exists_prodp
      (holds_on_pair2 raw_equiv)
      (andp
        (holds_on_pair (raw_data_item_sorted order))
        (holds_on_pair raw_data_item_ints_optimal)
      )
      (andp
        (holds_on_pair (raw_data_item_sorted order))
        (holds_on_pair raw_data_item_ints_optimal)
      )
      l1 l2;
    list_for_all_exists_implies
      (andp2
        (holds_on_pair2 raw_equiv)
        (prodp
          (andp
            (holds_on_pair (raw_data_item_sorted order))
            (holds_on_pair raw_data_item_ints_optimal)
          )
          (andp
            (holds_on_pair (raw_data_item_sorted order))
            (holds_on_pair raw_data_item_ints_optimal)
          )
        )
      )
      ( = )
      l1 l2
      (fun x1 x2 ->
        raw_equiv_sorted_optimal order (fst x1) (fst x2);
        raw_equiv_sorted_optimal order (snd x1) (snd x2)
      );
    list_for_all_exists_equal_eq l1 l2;
    list_for_all_exists_prodp
      (holds_on_pair2 raw_equiv)
      (andp
        (holds_on_pair (raw_data_item_sorted order))
        (holds_on_pair raw_data_item_ints_optimal)
      )
      (andp
        (holds_on_pair (raw_data_item_sorted order))
        (holds_on_pair raw_data_item_ints_optimal)
      )
      l2 l1;
    list_for_all_exists_implies
      (andp2
        (holds_on_pair2 raw_equiv)
        (prodp
          (andp
            (holds_on_pair (raw_data_item_sorted order))
            (holds_on_pair raw_data_item_ints_optimal)
          )
          (andp
            (holds_on_pair (raw_data_item_sorted order))
            (holds_on_pair raw_data_item_ints_optimal)
          )
        )
      )
      ( = )
      l2 l1
      (fun x2 x1 ->
        raw_equiv_sym (fst x2) (fst x1);
        raw_equiv_sorted_optimal order (fst x1) (fst x2);
        raw_equiv_sym (snd x2) (snd x1);
        raw_equiv_sorted_optimal order (snd x1) (snd x2)
      );
    list_for_all_exists_equal_eq l2 l1;
    list_sorted_ext_eq (map_entry_order order _) l1 l2

let rec raw_data_item_sorted_optimal_valid_aux
  (order: (raw_data_item -> raw_data_item -> bool) {
    order_irrefl order /\
    order_trans order
  })
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) l /\
    List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) l /\
    FStar.List.Tot.sorted (map_entry_order order _) l
  ))
  (ensures (
    list_no_setoid_repeats (map_entry_order raw_equiv _) l
  ))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    raw_data_item_sorted_optimal_valid_aux order q;
    if List.Tot.existsb (map_entry_order raw_equiv _ a) q
    then begin
      let a' = list_existsb_elim (map_entry_order raw_equiv _ a) q in
      list_sorted_memP (map_entry_order order _) a q a';
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) q;
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_ints_optimal)) q;
      raw_equiv_sorted_optimal order (fst a) (fst a')
    end
    else ()


let raw_data_item_sorted_optimal_valid
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (x1: raw_data_item)
: Lemma
  (requires (
    raw_data_item_sorted order x1 /\
    raw_data_item_ints_optimal x1
  ))
  (ensures (valid_raw_data_item x1))
= holds_on_raw_data_item_andp (raw_data_item_sorted_elem order) raw_data_item_ints_optimal_elem x1;
  holds_on_raw_data_item_implies
    (andp (raw_data_item_sorted_elem order) raw_data_item_ints_optimal_elem)
    valid_raw_data_item_elem
    (fun x ->
      match x with
      | Map len v ->
        holds_on_raw_data_item_andp (raw_data_item_sorted_elem order) raw_data_item_ints_optimal_elem x;
          holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) (Map len v);
          holds_on_raw_data_item_eq (raw_data_item_ints_optimal_elem) (Map len v);
          assert (List.Tot.for_all (holds_on_pair (holds_on_raw_data_item raw_data_item_ints_optimal_elem)) v);
          assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
          assert (List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) v);
          raw_data_item_sorted_optimal_valid_aux order v
      | _ -> ()
    )
    x1

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
