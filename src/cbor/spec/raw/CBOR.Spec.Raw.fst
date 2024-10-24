module CBOR.Spec.Raw
friend CBOR.Spec.API.Type

module R = CBOR.Spec.Raw.Sort
  
let mk_cbor r =
  if R.valid_raw_data_item r
  then begin
    R.raw_data_item_uint64_optimize_correct r;
    R.raw_data_item_uint64_optimize_valid r;
    let r' = R.raw_data_item_uint64_optimize r in
    R.cbor_raw_sort_correct r';
    R.cbor_raw_sort r'
  end
  else pack (CSimple 0uy) // dummy

let mk_cbor_equiv'
  (r: R.raw_data_item)
: Lemma
  (requires (R.valid_raw_data_item r == true))
  (ensures (R.raw_equiv r (mk_cbor r)))
= R.raw_data_item_uint64_optimize_equiv r;
  let r' = R.raw_data_item_uint64_optimize r in
  R.cbor_raw_sort_equiv r';
  R.raw_equiv_trans r r' (mk_cbor r)

let mk_cbor_equiv
  r1 r2
= mk_cbor_equiv' r1;
  mk_cbor_equiv' r2;
  R.raw_equiv_sym (mk_cbor r2) r2;
  R.raw_equiv_sym (mk_cbor r1) r1;
  Classical.move_requires (R.raw_equiv_trans r1 (mk_cbor r1)) (mk_cbor r2);
  Classical.move_requires (R.raw_equiv_trans r1 (mk_cbor r2)) r2;
  Classical.move_requires (R.raw_equiv_trans (mk_cbor r1) r1) r2;
  Classical.move_requires (R.raw_equiv_trans (mk_cbor r1) r2) (mk_cbor r2);
  Classical.move_requires (R.raw_equiv_sorted_optimal R.deterministically_encoded_cbor_map_key_order (mk_cbor r1)) (mk_cbor r2)

let mk_cbor_eq
  r
= assert_norm (R.valid_raw_data_item == R.holds_on_raw_data_item R.valid_raw_data_item_elem);
  R.holds_on_raw_data_item_eq R.valid_raw_data_item_elem r;
  mk_cbor_equiv' r;
  let r' = mk_cbor r in
  assert (R.raw_equiv r r' == true);
  R.raw_equiv_eq r r';
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem);
  assert_norm (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order));
  R.holds_on_raw_data_item_eq R.raw_data_item_ints_optimal_elem r';
  R.holds_on_raw_data_item_eq (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order) r';
  R.raw_data_item_sorted_optimal_valid R.deterministically_encoded_cbor_map_key_order r';
  R.holds_on_raw_data_item_eq R.valid_raw_data_item_elem r';
  match r, r' with
  | R.Tagged _ v, R.Tagged _ v' ->
    mk_cbor_equiv' v;
    R.raw_equiv_sym (mk_cbor v) v;
    R.raw_equiv_trans (mk_cbor v) v v';
    R.raw_equiv_sorted_optimal R.deterministically_encoded_cbor_map_key_order (mk_cbor v) v'
  | R.Array len v, R.Array len' v' ->
    List.Tot.for_all_mem R.valid_raw_data_item v;
    List.Tot.for_all_mem R.raw_data_item_ints_optimal v';
    List.Tot.for_all_mem (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order) v';
    U.list_for_all2_map2 R.raw_equiv v v' mk_cbor cast_to_cbor ( = ) (fun x x' ->
      mk_cbor_equiv' x;
      R.raw_equiv_sym (mk_cbor x) x;
      R.raw_equiv_trans (mk_cbor x) x x';
      R.raw_equiv_sorted_optimal R.deterministically_encoded_cbor_map_key_order (mk_cbor x) x'
    );
    U.list_for_all2_equals
      (List.Tot.map mk_cbor v)
      (List.Tot.map cast_to_cbor v')
  | R.Map _ v, R.Map _ v' ->
    let prf
      (x: R.raw_data_item)
    : Lemma
      (mk_cbor_match_map_elem v v' x)
      [SMTPat (mk_cbor_match_map_elem v v' x)]
    = if R.valid_raw_data_item x
      then begin
        mk_cbor_equiv' x;
        R.list_setoid_assoc_valid_equiv x v (mk_cbor x) v';
        R.list_setoid_assoc_sorted_optimal R.deterministically_encoded_cbor_map_key_order (mk_cbor x) v';
        match U.list_setoid_assoc R.raw_equiv x v, cbor_map_get v' (mk_cbor x) with
        | Some w, Some w' ->
          list_assoc_cbor v' (mk_cbor x);
          let Some x_ = U.list_setoid_assoc_mem R.raw_equiv x v in
          List.Tot.for_all_mem (U.holds_on_pair R.valid_raw_data_item) v;
          mk_cbor_equiv' w;
          R.raw_equiv_sym w (mk_cbor w);
          R.raw_equiv_trans (mk_cbor w) w w';
          R.raw_equiv_sorted_optimal R.deterministically_encoded_cbor_map_key_order (mk_cbor w) w'
        | _ -> ()
      end
    in
    cbor_map_length_eq v';
    ()
  | _ -> ()

let mk_det_raw_cbor c =
  R.raw_data_item_sorted_optimal_valid R.deterministically_encoded_cbor_map_key_order c;
  mk_cbor_equiv' c;
  R.raw_equiv_sorted_optimal R.deterministically_encoded_cbor_map_key_order c (mk_cbor c);
  c

(* NOTE: the following lemmas DO use the definition of mk_det_raw_cbor *)

let rec no_repeats_map_fst_mk_det_raw_cbor_map_entry
  (l: list (cbor & cbor))
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l)))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst (List.Tot.map mk_det_raw_cbor_map_entry l))))
= match l with
  | [] -> ()
  | a :: q ->
    CBOR.Spec.Util.list_memP_map_forall fst q;
    CBOR.Spec.Util.list_memP_map_forall mk_det_raw_cbor_map_entry q;
    CBOR.Spec.Util.list_memP_map_forall fst (List.Tot.map mk_det_raw_cbor_map_entry q);
    no_repeats_map_fst_mk_det_raw_cbor_map_entry q

let rec assoc_map_mk_det_raw_cbor_map_entry
  (l: list (cbor & cbor))
  (x: cbor)
: Lemma
  (match List.Tot.assoc x l, List.Tot.assoc x (List.Tot.map mk_det_raw_cbor_map_entry l) with
  | Some y, Some y' -> y == y'
  | None, None -> True
  | _ -> False)
= match l with
  | a :: q -> if x = fst a then () else begin
    assert (mk_cbor (fst (mk_det_raw_cbor_map_entry a)) == fst a);
    assoc_map_mk_det_raw_cbor_map_entry q x
  end
  | _ -> ()

let mk_det_raw_cbor_map
  l len
=
  let l1 = List.Tot.map mk_det_raw_cbor_map_entry l in
  CBOR.Spec.Util.list_memP_map_forall mk_det_raw_cbor_map_entry l;
  no_repeats_map_fst_mk_det_raw_cbor_map_entry l;
  RS.cbor_map_sort_correct l1;
  let l' = RS.cbor_map_sort l1 in
  let r = R.Map (R.mk_raw_uint64 len) l' in
  R.holds_on_raw_data_item_eq R.raw_data_item_ints_optimal_elem r;
  List.Tot.for_all_mem (CBOR.Spec.Util.holds_on_pair R.raw_data_item_ints_optimal) l';
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem);
  assert (R.raw_data_item_ints_optimal r);
  R.holds_on_raw_data_item_eq (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order) r;
  List.Tot.for_all_mem (CBOR.Spec.Util.holds_on_pair (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order)) l';
  assert_norm (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem R.deterministically_encoded_cbor_map_key_order));
  assert (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order r);
  R.raw_data_item_sorted_optimal_valid R.deterministically_encoded_cbor_map_key_order r;
  let res = mk_cbor r in
  mk_cbor_eq r;
  let CMap m = unpack res in
  mk_det_raw_cbor_mk_cbor r;
  assert (List.Tot.length l == FStar.UInt64.v len);
  assert (List.Tot.length l' == FStar.UInt64.v len);
  assert (cbor_map_length m == FStar.UInt64.v len);
  let prf
    (x: cbor)
  : Lemma
    (List.Tot.assoc x l == cbor_map_get m x)
  = let x' = mk_det_raw_cbor x in
    assert (mk_cbor_match_map_elem l' m x');
    RS.list_setoid_assoc_sorted_optimal R.deterministically_encoded_cbor_map_key_order x' l';
    assert (x' == x);
    assert (List.Tot.assoc x' l1 == List.Tot.assoc x' l');
    assoc_map_mk_det_raw_cbor_map_entry l x;
    assert (List.Tot.assoc x l == cbor_map_get m x)
  in
  Classical.forall_intro prf;
  assert (mk_det_raw_cbor res == R.Map (R.mk_raw_uint64 len) l');
  res
