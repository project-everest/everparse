module CBOR.Spec.Raw
friend CBOR.Spec.API.Type
friend CBOR.Spec.Raw.DataModel

module DM = CBOR.Spec.Raw.DataModel

let mk_cbor r =
  if R.valid_raw_data_item r
  then begin
    R.raw_data_item_uint64_optimize_correct r;
    R.raw_data_item_uint64_optimize_valid r ();
    let r' = R.raw_data_item_uint64_optimize r in
    R.cbor_raw_sort_correct RF.deterministically_encoded_cbor_map_key_order RF.cbor_compare r';
    let x' = R.cbor_raw_sort RF.deterministically_encoded_cbor_map_key_order RF.cbor_compare r' in
    assert (DM.cbor_bool RF.deterministically_encoded_cbor_map_key_order RF.cbor_compare x');
    x'
  end
  else pack (CSimple 0uy) // dummy

let mk_cbor_equiv'
  (r: R.raw_data_item)
: Lemma
  (requires (R.valid_raw_data_item r == true))
  (ensures (R.raw_equiv r (mk_cbor r)))
=
  R.raw_data_item_uint64_optimize_equiv r ();
  let r' = R.raw_data_item_uint64_optimize r in
  R.raw_data_item_uint64_optimize_correct r;
  R.cbor_raw_sort_equiv RF.deterministically_encoded_cbor_map_key_order RF.cbor_compare r';
  equiv_trans basic_data_model r r' (mk_cbor r)

let mk_cbor_equiv
  r1 r2
= mk_cbor_equiv' r1;
  mk_cbor_equiv' r2;
  equiv_sym basic_data_model (mk_cbor r2) r2;
  equiv_sym basic_data_model (mk_cbor r1) r1;
  Classical.move_requires (equiv_trans basic_data_model r1 (mk_cbor r1)) (mk_cbor r2);
  Classical.move_requires (equiv_trans basic_data_model r1 (mk_cbor r2)) r2;
  Classical.move_requires (equiv_trans basic_data_model (mk_cbor r1) r1) r2;
  Classical.move_requires (equiv_trans basic_data_model (mk_cbor r1) r2) (mk_cbor r2);
  Classical.move_requires (R.raw_equiv_sorted_optimal RF.deterministically_encoded_cbor_map_key_order (mk_cbor r1)) (mk_cbor r2)

let mk_cbor_eq
  r
= valid_eq basic_data_model r;
  valid_eq' basic_data_model r;
  R.holds_on_raw_data_item_eq R.valid_raw_data_item_elem r;
  mk_cbor_equiv' r;
  let r' = mk_cbor r in
  assert (R.raw_equiv r r' == true);
  R.equiv_eq basic_data_model r r';
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem);
  assert_norm (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem RF.deterministically_encoded_cbor_map_key_order));
  R.holds_on_raw_data_item_eq R.raw_data_item_ints_optimal_elem r';
  R.holds_on_raw_data_item_eq (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order) r';
  R.raw_data_item_sorted_optimal_valid RF.deterministically_encoded_cbor_map_key_order r';
  R.holds_on_raw_data_item_eq R.valid_raw_data_item_elem r';
  R.raw_equiv_eq_valid r r';
  R.raw_data_item_uint64_optimize_map_length r;
  R.raw_data_item_uint64_optimize_valid r ();
  R.raw_data_item_uint64_optimize_correct r;
  R.cbor_raw_sort_correct RF.deterministically_encoded_cbor_map_key_order RF.cbor_compare (R.raw_data_item_uint64_optimize r);
  match r, r' with
  | R.Tagged tag v, R.Tagged tag' v' ->
    mk_cbor_equiv' v;
    R.equiv_sym basic_data_model (mk_cbor v) v;
    R.equiv_trans basic_data_model (mk_cbor v) v v';
    R.raw_equiv_sorted_optimal RF.deterministically_encoded_cbor_map_key_order (mk_cbor v) v';
    ()
  | R.Array len v, R.Array len' v' ->
    List.Tot.for_all_mem R.valid_raw_data_item v;
    List.Tot.for_all_mem R.raw_data_item_ints_optimal v';
    List.Tot.for_all_mem (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order) v';
    U.list_for_all2_map2 R.raw_equiv v v' mk_cbor (DM.cast_to_cbor RF.deterministically_encoded_cbor_map_key_order RF.cbor_compare) ( = ) (fun x x' ->
      mk_cbor_equiv' x;
      R.equiv_sym basic_data_model (mk_cbor x) x;
      R.equiv_trans basic_data_model (mk_cbor x) x x';
      R.raw_equiv_sorted_optimal RF.deterministically_encoded_cbor_map_key_order (mk_cbor x) x'
    );
    U.list_for_all2_equals
      (List.Tot.map mk_cbor v)
      (List.Tot.map (DM.cast_to_cbor RF.deterministically_encoded_cbor_map_key_order RF.cbor_compare) v')
  | R.Map len v, R.Map len' v' ->
    valid_eq basic_data_model r';
    let prf
      (x: R.raw_data_item)
    : Lemma
      (mk_cbor_match_map_elem v v' x)
      [SMTPat (mk_cbor_match_map_elem v v' x)]
    = if R.valid_raw_data_item x
      then begin
        mk_cbor_equiv' x;
        R.list_setoid_assoc_valid_equiv x v (mk_cbor x) v';
        R.list_setoid_assoc_sorted_optimal RF.deterministically_encoded_cbor_map_key_order (mk_cbor x) v';
        match U.list_setoid_assoc R.raw_equiv x v, cbor_map_get v' (mk_cbor x) with
        | Some w, Some w' ->
          DM.list_assoc_cbor #RF.deterministically_encoded_cbor_map_key_order #RF.cbor_compare v' (mk_cbor x);
          let Some x_ = U.list_setoid_assoc_mem R.raw_equiv x v in
          List.Tot.for_all_mem (U.holds_on_pair R.valid_raw_data_item) v;
          R.raw_data_item_sorted_optimal_valid RF.deterministically_encoded_cbor_map_key_order w';
          equiv_eq basic_data_model w w';
          mk_cbor_equiv' w;
          R.raw_equiv_sym w (mk_cbor w);
          R.raw_equiv_trans (mk_cbor w) w w';
          R.raw_equiv_sorted_optimal RF.deterministically_encoded_cbor_map_key_order (mk_cbor w) w'
        | _ -> ()
      end
    in
    DM.cbor_map_length_eq #RF.deterministically_encoded_cbor_map_key_order #RF.cbor_compare v';
    assert (len.value == len'.value);
    assert (List.Tot.length v == List.Tot.length v');
    assert (mk_cbor_match_map v v');
    ()
  | _ -> ()

let mk_det_raw_cbor c =
  R.raw_data_item_sorted_optimal_valid RF.deterministically_encoded_cbor_map_key_order c;
  mk_cbor_equiv' c;
  R.raw_equiv_sorted_optimal RF.deterministically_encoded_cbor_map_key_order c (mk_cbor c);
  c

(* NOTE: the following lemmas DO use the definition of mk_det_raw_cbor *)

let rec no_repeats_map_fst_mk_det_raw_cbor_map_entry
  (l: list (cbor & cbor))
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
  RS.cbor_map_sort_correct RF.deterministically_encoded_cbor_map_key_order RF.cbor_compare l1;
  let l' = RS.cbor_map_sort RF.deterministically_encoded_cbor_map_key_order l1 in
  let r = R.Map (R.mk_raw_uint64 len) l' in
  R.holds_on_raw_data_item_eq R.raw_data_item_ints_optimal_elem r;
  List.Tot.for_all_mem (CBOR.Spec.Util.holds_on_pair R.raw_data_item_ints_optimal) l';
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem);
  assert (R.raw_data_item_ints_optimal r);
  R.holds_on_raw_data_item_eq (R.raw_data_item_sorted_elem RF.deterministically_encoded_cbor_map_key_order) r;
  List.Tot.for_all_mem (CBOR.Spec.Util.holds_on_pair (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order)) l';
  assert_norm (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order == R.holds_on_raw_data_item (R.raw_data_item_sorted_elem RF.deterministically_encoded_cbor_map_key_order));
  assert (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order r);
  R.raw_data_item_sorted_optimal_valid RF.deterministically_encoded_cbor_map_key_order r;
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
    RS.list_setoid_assoc_sorted_optimal RF.deterministically_encoded_cbor_map_key_order x' l';
    assert (x' == x);
    assert (List.Tot.assoc x' l1 == List.Tot.assoc x' l');
    assoc_map_mk_det_raw_cbor_map_entry l x;
    assert (List.Tot.assoc x l == cbor_map_get m x)
  in
  Classical.forall_intro prf;
  assert (mk_det_raw_cbor res == R.Map (R.mk_raw_uint64 len) l');
  res

let mk_det_raw_cbor_map_raw m =
  DM.cbor_map_length_eq #RF.deterministically_encoded_cbor_map_key_order #RF.cbor_compare m;
  m

let mk_det_raw_cbor_map_raw_singleton key value = ()

let mk_det_raw_cbor_map_raw_assoc m k =
  let x = mk_det_raw_cbor k in
  RS.list_setoid_assoc_sorted_optimal RF.deterministically_encoded_cbor_map_key_order x m;
  assert (U.list_setoid_assoc R.raw_equiv x m == List.Tot.assoc x m);
  match List.Tot.assoc x m, cbor_map_get m (mk_cbor x) with
  | Some v1, Some v2 ->
    DM.list_assoc_cbor #RF.deterministically_encoded_cbor_map_key_order #RF.cbor_compare m x;
    R.raw_data_item_sorted_optimal_valid RF.deterministically_encoded_cbor_map_key_order v1;
    assert (R.valid_raw_data_item v1);
    mk_det_raw_cbor_mk_cbor v1;
    assert (mk_cbor v1 == v2)
  | _ -> ()

let mk_det_raw_cbor_map_raw_mem m x =
  let l = mk_det_raw_cbor_map_raw m in
  List.Tot.for_all_mem (U.holds_on_pair (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order)) l;
  List.Tot.for_all_mem (U.holds_on_pair R.raw_data_item_ints_optimal) l;
  CBOR.Spec.Raw.Map.list_sorted_map_entry_order_no_repeats RF.deterministically_encoded_cbor_map_key_order l;
  U.list_assoc_no_repeats_mem l (fst x) (snd x);
  let prf1 () : Lemma
    (requires (
      List.Tot.memP x l
    ))
    (ensures (
      U.holds_on_pair (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order) x /\
      U.holds_on_pair R.raw_data_item_ints_optimal x /\
      cbor_map_get m (mk_cbor (fst x)) == Some (mk_cbor (snd x))
    ))
  = assert (U.holds_on_pair (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order) x);
    assert (U.holds_on_pair R.raw_data_item_ints_optimal x);
    mk_det_raw_cbor_mk_cbor (fst x);
    mk_det_raw_cbor_mk_cbor (snd x);
    assert (cbor_map_get m (mk_cbor (fst x)) == Some (mk_cbor (snd x)))
  in
  let prf2 () : Lemma
    (requires (
      U.holds_on_pair (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order) x /\
      U.holds_on_pair R.raw_data_item_ints_optimal x /\
      cbor_map_get m (mk_cbor (fst x)) == Some (mk_cbor (snd x))
    ))
    (ensures (
      List.Tot.memP x l
    ))
  =
    mk_det_raw_cbor_mk_cbor (fst x);
    mk_det_raw_cbor_mk_cbor (snd x)
  in
  Classical.move_requires prf1 ();
  Classical.move_requires prf2 ()

let mk_cbor_eq_map x = ()

#push-options "--z3rlimit 32 --split_queries always"

#restart-solver

let mk_det_raw_cbor_map_raw_snoc m key value =
  mk_det_raw_cbor_map_raw_assoc m key;
  let l = mk_det_raw_cbor_map_raw m in
  R.list_setoid_assoc_sorted_optimal RF.deterministically_encoded_cbor_map_key_order (mk_det_raw_cbor key) l;
  List.Tot.assoc_mem (mk_det_raw_cbor key) l;
  assert (Some? (List.Tot.assoc (mk_det_raw_cbor key) l) <==> cbor_map_defined key m);
  let kv = (mk_det_raw_cbor key, mk_det_raw_cbor value) in
  CBOR.Spec.Raw.Map.map_insert_sorted RF.deterministically_encoded_cbor_map_key_order RF.cbor_compare l kv;
  match CBOR.Spec.Raw.Map.map_insert RF.cbor_compare l kv with
  | None -> ()
  | Some l' ->
    let m' = cbor_map_union m (cbor_map_singleton key value) in
    let l2 = (mk_det_raw_cbor_map_raw m') in
    let prf
      (x: (raw_data_item & raw_data_item))
    : Lemma
      (List.Tot.memP x l' <==> List.Tot.memP x l2)
    =
      CBOR.Spec.Raw.Map.map_insert_mem RF.cbor_compare m kv x;
      mk_det_raw_cbor_map_raw_mem m' x;
      mk_det_raw_cbor_map_raw_mem m x;
      if
        U.holds_on_pair (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order) x &&
        U.holds_on_pair R.raw_data_item_ints_optimal x
      then begin
        mk_det_raw_cbor_mk_cbor (fst x);
        mk_det_raw_cbor_mk_cbor (snd x)
      end
      else ()
    in
    Classical.forall_intro prf;
    U.list_sorted_ext_eq
      (map_entry_order RF.deterministically_encoded_cbor_map_key_order _)
      l'
      l2;
    List.Tot.assoc_mem (mk_det_raw_cbor key) l;
    assert (Some? (List.Tot.assoc (mk_det_raw_cbor key) l) <==> List.Tot.memP (mk_det_raw_cbor key) (List.Tot.map fst l));
    assert (mk_det_raw_cbor_map_raw_snoc_post m key value);
    ()

#pop-options
