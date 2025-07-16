module CBOR.Spec.Raw.Sort
open CBOR.Spec.Raw.Map

let cbor_map_sort order = map_sort order

let cbor_map_sort_eq
  order
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (cbor_map_sort order l == map_sort order l)
= ()

let cbor_map_sort_correct order compare x =
  map_sort_correct order compare x

let cbor_raw_sort_elem_ints_optimal
  order compare
  (x: raw_data_item)
: Lemma
  (requires (raw_data_item_ints_optimal x == true))
  (ensures (raw_data_item_ints_optimal (cbor_raw_sort_elem order compare x) == true))
= assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem (cbor_raw_sort_elem order compare x);
  match x with
  | Map len v ->
    list_for_all_intro (holds_on_pair raw_data_item_ints_optimal) (cbor_map_sort_failsafe order v) (fun x ->
      List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v;
      cbor_map_sort_failsafe_correct order compare v;
      ()
    )
  | _ -> ()

let cbor_raw_sort_elem_equiv
  order compare
  (x: raw_data_item)
: Lemma
  (requires (valid basic_data_model x /\
    raw_data_item_ints_optimal x /\
    pre_holds_on_raw_data_item (raw_data_item_sorted_elem order) x
  ))
  (ensures (let x' = cbor_raw_sort_elem order compare x in
    valid basic_data_model x' /\
    raw_data_item_ints_optimal x' /\
    raw_data_item_sorted order x' /\
    raw_equiv x x' == true
  ))
= let x' = cbor_raw_sort_elem order compare x in
  valid_eq basic_data_model x;
  valid_eq basic_data_model x';
  equiv_eq basic_data_model x x';
  cbor_raw_sort_elem_ints_optimal order compare x;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x';
  equiv_refl_forall basic_data_model;
  match x with
  | Map _ v ->
    List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) v;
    List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v;
    list_no_setoid_repeats_ext raw_equiv ( = ) (List.Tot.map fst v) (fun l1 l2 x1 x2 ->
      List.Tot.append_memP l1 l2 x1;
      List.Tot.append_memP l1 l2 x2;
      let y1 = list_memP_map_elim fst x1 v in
      let y2 = list_memP_map_elim fst x2 v in
      raw_equiv_sorted_optimal_eq order x1 x2
    );
    list_no_setoid_repeats_no_repeats (List.Tot.map fst v);
    cbor_map_sort_correct order compare v;
    let Map _ v' = x' in
    list_for_all_intro (holds_on_pair (raw_data_item_sorted order)) v' (fun _ -> ());
    raw_data_item_sorted_optimal_valid order x';
    list_assoc_sorted_optimal_setoid_assoc_eq order v v';
    list_assoc_sorted_optimal_setoid_assoc_eq order v' v
  | _ -> raw_equiv_refl x

let cbor_raw_sort_ints_optimal
  order compare
  (x: raw_data_item)
: Lemma
  (requires (raw_data_item_ints_optimal x == true))
  (ensures (raw_data_item_ints_optimal (cbor_raw_sort order compare x) == true))
= holds_on_raw_data_item_fmap_inv
    (cbor_raw_sort_elem order compare)
    raw_data_item_ints_optimal_elem
    (fun x -> holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x)
    (fun x -> cbor_raw_sort_elem_ints_optimal order compare x)
    x

let rec cbor_raw_sort_correct
  order compare
  (x: raw_data_item)
: Lemma
  (requires (raw_data_item_ints_optimal x == true /\
    valid_raw_data_item x == true
  ))
  (ensures (
    let x' = cbor_raw_sort order compare x in
    raw_data_item_ints_optimal x' == true /\
    raw_data_item_sorted order x' == true /\
    valid_raw_data_item x'  == true /\
    raw_equiv x x' /\
    begin match x, x' with
    | Map len _, Map len' _ -> len.value == len'.value
    | Map _ _, _ | _, Map _ _ -> False
    | _ -> True
    end
  ))
  (decreases (raw_data_item_size x))
= let x' = cbor_raw_sort order compare x in
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x;
  valid_eq basic_data_model x;
  holds_on_raw_data_item_eq (valid_item basic_data_model) x;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x';
  valid_eq basic_data_model x';
  holds_on_raw_data_item_eq (valid_item basic_data_model) x';
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x';
  Classical.move_requires (raw_equiv_eq_valid x) x';
  raw_data_item_fmap_eq (cbor_raw_sort_elem order compare) x;
  raw_data_item_size_eq x;
  assert_norm (cbor_raw_sort order compare == raw_data_item_fmap (cbor_raw_sort_elem order compare));
  match x with
  | Tagged _ v -> cbor_raw_sort_correct order compare v; ()
  | Array _ v ->
    List.Tot.for_all_mem valid_raw_data_item v;
    List.Tot.for_all_mem raw_data_item_ints_optimal v;
    List.Tot.for_all_mem (raw_data_item_sorted order) v;
    let Array _ v' = x' in
    list_for_all_intro raw_data_item_ints_optimal v' (fun x ->
      let y = list_memP_map_elim (cbor_raw_sort order compare) x v in
      list_sum_memP raw_data_item_size v y;
      cbor_raw_sort_correct order compare y;
      ()
    );
    list_for_all_intro (raw_data_item_sorted order) v' (fun x ->
      let y = list_memP_map_elim (cbor_raw_sort order compare) x v in
      list_sum_memP raw_data_item_size v y;
      cbor_raw_sort_correct order compare y
    );
    raw_data_item_sorted_optimal_valid order x';
    list_for_all2_map (cbor_raw_sort order compare) v raw_equiv2 (fun y ->
      list_sum_memP raw_data_item_size v y;
      cbor_raw_sort_correct order compare y
    );
    ()
  | Map len v ->
    list_of_pair_list_map valid_raw_data_item v;
    List.Tot.for_all_mem (holds_on_pair valid_raw_data_item) v;
    List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v;
    List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) v;
    list_for_all_intro (holds_on_pair (holds_on_raw_data_item (valid_item basic_data_model))) v (fun x ->
      valid_eq' basic_data_model (fst x);
      valid_eq' basic_data_model (snd x)
    );
    valid_raw_data_item_map_fmap_equiv basic_data_model (cbor_raw_sort order compare) v (fun x ->
      let y = list_memP_map_elim fst x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct order compare x
    );
    let v1 = List.Tot.map (apply_on_pair (cbor_raw_sort order compare)) v in
    let x1 = Map len v1 in
    list_for_all_intro (holds_on_pair raw_data_item_ints_optimal) v1 (fun x ->
      let x : (raw_data_item & raw_data_item) = x in
      let y = list_memP_map_elim (apply_on_pair (cbor_raw_sort order compare)) x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct order compare (fst y);
      cbor_raw_sort_correct order compare (snd y);
      ()
    );
    list_for_all_intro (holds_on_pair (raw_data_item_sorted order)) v1 (fun x ->
      let x : (raw_data_item & raw_data_item) = x in
      let y = list_memP_map_elim (apply_on_pair (cbor_raw_sort order compare)) x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct order compare (fst y);
      cbor_raw_sort_correct order compare (snd y);
      ()
    );
    list_of_pair_list_map valid_raw_data_item v1;
    List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v1;
    List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) v1;
    list_for_all_intro (holds_on_pair valid_raw_data_item) v1 (fun x ->
      raw_data_item_sorted_optimal_valid order (fst x);
      raw_data_item_sorted_optimal_valid order (snd x)
    );
    valid_eq basic_data_model x1;
    raw_equiv_eq_valid x x1;
    equiv_refl_forall basic_data_model;
    equiv_sym_forall basic_data_model;
    equiv_trans_forall basic_data_model;
    list_setoid_assoc_eq_refl raw_equiv raw_equiv v;
    list_map_fst_apply_on_pair (cbor_raw_sort order compare) v;
    list_map_snd_apply_on_pair (cbor_raw_sort order compare) v;
    list_for_all2_map (cbor_raw_sort order compare) (List.Tot.map fst v) raw_equiv (fun x ->
      let y = list_memP_map_elim fst x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct order compare x
    );
    list_for_all2_map (cbor_raw_sort order compare) (List.Tot.map snd v) raw_equiv (fun x ->
      let y = list_memP_map_elim snd x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct order compare x
    );
    list_setoid_assoc_eq_equiv1 raw_equiv raw_equiv v v1 v;
    list_setoid_assoc_eq_equiv2 raw_equiv raw_equiv v v v1;
    cbor_raw_sort_elem_equiv order compare x1;
    ()
  | _ -> ()
