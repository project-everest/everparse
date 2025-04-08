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
  (requires (valid basic_data_model x))
  (ensures (let x' = cbor_raw_sort_elem x in
    valid basic_data_model x' /\
    raw_equiv x x' == true
  ))
= let x' = cbor_raw_sort_elem x in
  valid_eq basic_data_model x;
  valid_eq basic_data_model x';
  equiv_eq basic_data_model x x';
  if x = x'
  then ()
  else begin
    match x with
    | Map len v -> assume False
    | _ -> raw_equiv_refl x
  end

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

let cbor_raw_sort_correct
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
= admit ()
(*
holds_on_raw_data_item_andp raw_data_item_ints_optimal_elem (valid_item basic_data_model) x;
  valid_eq' basic_data_model x;
  valid_eq' basic_data_model (cbor_raw_sort x);
  let phi = andp raw_data_item_ints_optimal_elem
    (valid_item basic_data_model) in
  let so = raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order in
  holds_on_raw_data_item_fmap_gen
    cbor_raw_sort_elem
    phi
    so
    (fun x ->
      let x' = pre_raw_data_item_fmap cbor_raw_sort_elem x in
      holds_on_raw_data_item_eq phi x;
      pre_holds_on_raw_data_item_implies (phi `andp` so) phi (fun _ -> ()) x';
      match x with
      | Map _ v ->
        valid_raw_data_item_map_fmap_equiv
          basic_data_model
          (raw_data_item_fmap cbor_raw_sort_elem)
          v
          (fun x -> cbor_raw_sort_equiv x)
      | _ -> ()
    )
    (fun x ->
      holds_on_raw_data_item_andp raw_data_item_ints_optimal_elem (valid_item basic_data_model) x;
      let x' = cbor_raw_sort_elem x in
      holds_on_raw_data_item_andp phi so x';
      holds_on_raw_data_item_andp raw_data_item_ints_optimal_elem (valid_item basic_data_model) x';
      cbor_raw_sort_elem_ints_optimal x;
      match x with
      | Map len v ->
        valid_raw_data_item_map_no_repeats v;
        cbor_map_sort_failsafe_correct v;
        list_for_all_intro (holds_on_pair (holds_on_raw_data_item so)) (cbor_map_sort_failsafe v) (fun _ ->
          List.Tot.for_all_mem (holds_on_pair (holds_on_raw_data_item so)) v
        );
        raw_data_item_sorted_optimal_valid deterministically_encoded_cbor_map_key_order x'
      | _ -> ()
    )
    x;
  let x' = cbor_raw_sort x in
  holds_on_raw_data_item_andp phi (raw_data_item_sorted_elem deterministically_encoded_cbor_map_key_order) x';
  holds_on_raw_data_item_andp raw_data_item_ints_optimal_elem (valid_item basic_data_model) x'
*)
