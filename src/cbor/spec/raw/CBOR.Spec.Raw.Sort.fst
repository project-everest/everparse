module CBOR.Spec.Raw.Sort
open CBOR.Spec.Raw.Map

let cbor_map_sort = map_sort deterministically_encoded_cbor_map_key_order

let cbor_map_sort_eq
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (cbor_map_sort l == map_sort deterministically_encoded_cbor_map_key_order l)
= ()

let cbor_map_sort_correct x =
  cbor_map_sort_eq x;
  Classical.forall_intro_2 deterministically_encoded_cbor_map_key_order_spec;
  Classical.forall_intro_2 cbor_compare_correct;
  Classical.forall_intro_2 cbor_compare_equal;
  Classical.forall_intro_2 bytes_lex_compare_opp;
  map_sort_correct deterministically_encoded_cbor_map_key_order cbor_compare x

let cbor_raw_sort_elem_ints_optimal
  (x: raw_data_item)
: Lemma
  (requires (raw_data_item_ints_optimal x == true))
  (ensures (raw_data_item_ints_optimal (cbor_raw_sort_elem x) == true))
= assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem (cbor_raw_sort_elem x);
  match x with
  | Map len v ->
    list_for_all_intro (holds_on_pair raw_data_item_ints_optimal) (cbor_map_sort_failsafe v) (fun x ->
      List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v
    )
  | _ -> ()

let cbor_raw_sort_elem_equiv
  (x: raw_data_item)
: Lemma
  (requires (valid basic_data_model x /\
    raw_data_item_ints_optimal x /\
    pre_holds_on_raw_data_item (raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order) x
  ))
  (ensures (let x' = cbor_raw_sort_elem x in
    valid basic_data_model x' /\
    raw_data_item_ints_optimal x' /\
    raw_data_item_sorted deterministically_encoded_cbor_map_key_order x' /\
    raw_equiv x x' == true
  ))
= let x' = cbor_raw_sort_elem x in
  valid_eq basic_data_model x;
  valid_eq basic_data_model x';
  equiv_eq basic_data_model x x';
  cbor_raw_sort_elem_ints_optimal x;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order) x';
  equiv_refl_forall basic_data_model;
  match x with
  | Map _ v ->
    List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted deterministically_encoded_cbor_map_key_order)) v;
    List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v;
    list_no_setoid_repeats_ext raw_equiv ( = ) (List.Tot.map fst v) (fun l1 l2 x1 x2 ->
      List.Tot.append_memP l1 l2 x1;
      List.Tot.append_memP l1 l2 x2;
      let y1 = list_memP_map_elim fst x1 v in
      let y2 = list_memP_map_elim fst x2 v in
      raw_equiv_sorted_optimal_eq deterministically_encoded_cbor_map_key_order x1 x2
    );
    list_no_setoid_repeats_no_repeats (List.Tot.map fst v);
    cbor_map_sort_correct v;
    let Map _ v' = x' in
    list_for_all_intro (holds_on_pair (raw_data_item_sorted deterministically_encoded_cbor_map_key_order)) v' (fun _ -> ());
    raw_data_item_sorted_optimal_valid deterministically_encoded_cbor_map_key_order x';
    list_assoc_sorted_optimal_setoid_assoc_eq deterministically_encoded_cbor_map_key_order v v';
    list_assoc_sorted_optimal_setoid_assoc_eq deterministically_encoded_cbor_map_key_order v' v
  | _ -> raw_equiv_refl x

let cbor_raw_sort_ints_optimal
  (x: raw_data_item)
: Lemma
  (requires (raw_data_item_ints_optimal x == true))
  (ensures (raw_data_item_ints_optimal (cbor_raw_sort x) == true))
= holds_on_raw_data_item_fmap_inv
    cbor_raw_sort_elem
    raw_data_item_ints_optimal_elem
    (fun x -> holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x)
    (fun x -> cbor_raw_sort_elem_ints_optimal x)
    x

let rec cbor_raw_sort_correct
  (x: raw_data_item)
: Lemma
  (requires (raw_data_item_ints_optimal x == true /\
    valid_raw_data_item x == true
  ))
  (ensures (
    let x' = cbor_raw_sort x in
    raw_data_item_ints_optimal x' == true /\
    raw_data_item_sorted deterministically_encoded_cbor_map_key_order x' == true /\
    valid_raw_data_item x'  == true /\
    raw_equiv x x' /\
    begin match x, x' with
    | Map len _, Map len' _ -> len.value == len'.value
    | Map _ _, _ | _, Map _ _ -> False
    | _ -> True
    end
  ))
  (decreases (raw_data_item_size x))
= let x' = cbor_raw_sort x in
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x;
  valid_eq basic_data_model x;
  holds_on_raw_data_item_eq (valid_item basic_data_model) x;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order) x;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x';
  valid_eq basic_data_model x';
  holds_on_raw_data_item_eq (valid_item basic_data_model) x';
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order) x';
  Classical.move_requires (raw_equiv_eq_valid x) x';
  raw_data_item_fmap_eq cbor_raw_sort_elem x;
  raw_data_item_size_eq x;
  assert_norm (cbor_raw_sort == raw_data_item_fmap cbor_raw_sort_elem);
  match x with
  | Tagged _ v -> cbor_raw_sort_correct v; ()
  | Array _ v ->
    List.Tot.for_all_mem valid_raw_data_item v;
    List.Tot.for_all_mem raw_data_item_ints_optimal v;
    List.Tot.for_all_mem (raw_data_item_sorted deterministically_encoded_cbor_map_key_order) v;
    let Array _ v' = x' in
    list_for_all_intro raw_data_item_ints_optimal v' (fun x ->
      let y = list_memP_map_elim cbor_raw_sort x v in
      list_sum_memP raw_data_item_size v y;
      cbor_raw_sort_correct y;
      ()
    );
    list_for_all_intro (raw_data_item_sorted deterministically_encoded_cbor_map_key_order) v' (fun x ->
      let y = list_memP_map_elim cbor_raw_sort x v in
      list_sum_memP raw_data_item_size v y;
      cbor_raw_sort_correct y
    );
    raw_data_item_sorted_optimal_valid deterministically_encoded_cbor_map_key_order x';
    list_for_all2_map cbor_raw_sort v raw_equiv2 (fun y ->
      list_sum_memP raw_data_item_size v y;
      cbor_raw_sort_correct y
    );
    ()
  | Map len v ->
    list_of_pair_list_map valid_raw_data_item v;
    List.Tot.for_all_mem (holds_on_pair valid_raw_data_item) v;
    List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v;
    List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted deterministically_encoded_cbor_map_key_order)) v;
    list_for_all_intro (holds_on_pair (holds_on_raw_data_item (valid_item basic_data_model))) v (fun x ->
      valid_eq' basic_data_model (fst x);
      valid_eq' basic_data_model (snd x)
    );
    valid_raw_data_item_map_fmap_equiv basic_data_model cbor_raw_sort v (fun x ->
      let y = list_memP_map_elim fst x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct x
    );
    let v1 = List.Tot.map (apply_on_pair cbor_raw_sort) v in
    let x1 = Map len v1 in
    list_for_all_intro (holds_on_pair raw_data_item_ints_optimal) v1 (fun x ->
      let x : (raw_data_item & raw_data_item) = x in
      let y = list_memP_map_elim (apply_on_pair cbor_raw_sort) x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct (fst y);
      cbor_raw_sort_correct (snd y);
      ()
    );
    list_for_all_intro (holds_on_pair (raw_data_item_sorted deterministically_encoded_cbor_map_key_order)) v1 (fun x ->
      let x : (raw_data_item & raw_data_item) = x in
      let y = list_memP_map_elim (apply_on_pair cbor_raw_sort) x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct (fst y);
      cbor_raw_sort_correct (snd y);
      ()
    );
    list_of_pair_list_map valid_raw_data_item v1;
    List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v1;
    List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted deterministically_encoded_cbor_map_key_order)) v1;
    list_for_all_intro (holds_on_pair valid_raw_data_item) v1 (fun x ->
      raw_data_item_sorted_optimal_valid deterministically_encoded_cbor_map_key_order (fst x);
      raw_data_item_sorted_optimal_valid deterministically_encoded_cbor_map_key_order (snd x)
    );
    valid_eq basic_data_model x1;
    raw_equiv_eq_valid x x1;
    equiv_refl_forall basic_data_model;
    equiv_sym_forall basic_data_model;
    equiv_trans_forall basic_data_model;
    list_setoid_assoc_eq_refl raw_equiv raw_equiv v;
    list_map_fst_apply_on_pair cbor_raw_sort v;
    list_map_snd_apply_on_pair cbor_raw_sort v;
    list_for_all2_map cbor_raw_sort (List.Tot.map fst v) raw_equiv (fun x ->
      let y = list_memP_map_elim fst x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct x
    );
    list_for_all2_map cbor_raw_sort (List.Tot.map snd v) raw_equiv (fun x ->
      let y = list_memP_map_elim snd x v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v y;
      cbor_raw_sort_correct x
    );
    list_setoid_assoc_eq_equiv1 raw_equiv raw_equiv v v1 v;
    list_setoid_assoc_eq_equiv2 raw_equiv raw_equiv v v v1;
    cbor_raw_sort_elem_equiv x1;
    ()
  | _ -> ()
