module CBOR.Spec.API.Format
module RV = CBOR.Spec.Raw.Optimal
module RF = CBOR.Spec.Raw.Format
module RS = CBOR.Spec.Raw.Sort
module R = CBOR.Spec.Raw

let cbor_parse x =
  match RF.parse_cbor x with
  | None -> None
  | Some (y, n) ->
    if RV.valid_raw_data_item y
    then Some (R.mk_cbor y, n)
    else None

let cbor_parse_prefix x =
  RF.parse_cbor_prefix x

let cbor_det_serialize x =
  RF.serialize_cbor (R.mk_det_raw_cbor x)

let cbor_det_parse x =
  match RF.parse_cbor x with
  | None -> None
  | Some (y, n) ->
    if RV.raw_data_item_ints_optimal y && RS.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order y
    then begin
      RV.raw_data_item_sorted_optimal_valid RF.deterministically_encoded_cbor_map_key_order y;
      R.mk_det_raw_cbor_mk_cbor y;
      Some (R.mk_cbor y, n)
    end
    else None

let cbor_det_parse_prefix x =
  RF.parse_cbor_prefix x

let cbor_det_serialize_parse x =
  RF.serialize_parse_cbor (R.mk_det_raw_cbor x)

let cbor_det_serialize_tag tag =
  RF.serialize_cbor_tag (RV.mk_raw_uint64 tag)

let cbor_det_serialize_tag_length tag =
  RF.serialize_cbor_tag_length (RV.mk_raw_uint64 tag)

let cbor_det_serialize_tag_correct tag payload =
  let x = (R.Tagged (RV.mk_raw_uint64 tag) (R.mk_det_raw_cbor payload)) in
  R.valid_eq R.basic_data_model x;
  R.mk_cbor_eq x;
  R.mk_det_raw_cbor_mk_cbor x;
  assert (R.mk_det_raw_cbor (pack (CTagged tag payload)) == x);
  RF.serialize_cbor_tag_correct (RV.mk_raw_uint64 tag) (R.mk_det_raw_cbor payload)

let rec list_map_mk_det_raw_cbor_correct
  (l: list cbor)
: Lemma
  (ensures (
    let l' = List.Tot.map R.mk_det_raw_cbor l in
    List.Tot.for_all R.raw_data_item_ints_optimal l' /\
    List.Tot.for_all (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order) l'
  ))
= match l with
  | [] -> ()
  | _ :: q -> list_map_mk_det_raw_cbor_correct q

let rec list_map_mk_cbor_mk_det_raw_cbor
  (l: list cbor)
: Lemma
  (ensures (
    List.Tot.map R.mk_cbor (List.Tot.map R.mk_det_raw_cbor l) == l
  ))
= match l with
  | [] -> ()
  | _ :: q -> list_map_mk_cbor_mk_det_raw_cbor q

let cbor_det_serialize_list l =
  RF.serialize_cbor_list (List.Tot.map R.mk_det_raw_cbor l)

let cbor_det_serialize_list_nil () =
  RF.serialize_cbor_list_nil ()

let cbor_det_serialize_list_cons a q =
  RF.serialize_cbor_list_cons (R.mk_det_raw_cbor a) (List.Tot.map R.mk_det_raw_cbor q)

let cbor_det_serialize_array_length_gt_list l =
  let len = R.mk_raw_uint64 (U64.uint_to_t (List.Tot.length l)) in
  assert (RV.raw_uint64_optimal len);
  let l' = List.Tot.map R.mk_det_raw_cbor l in
  RF.serialize_cbor_array_length_gt_list len l';
  let x = R.Array len l' in
  list_map_mk_cbor_mk_det_raw_cbor l;
  list_map_mk_det_raw_cbor_correct l;
  assert_norm (R.raw_data_item_ints_optimal == R.holds_on_raw_data_item R.raw_data_item_ints_optimal_elem); // FIXME: WHY WHY WHY?
  R.raw_data_item_sorted_optimal_valid RF.deterministically_encoded_cbor_map_key_order x;
  R.mk_cbor_eq x;
  R.mk_det_raw_cbor_mk_cbor x;
  assert (R.mk_det_raw_cbor (pack (CArray l)) == x)

let cbor_det_serialize_string_length_gt ty l =
  let len = R.mk_raw_uint64 (U64.uint_to_t (Seq.length l)) in
  assert (RV.raw_uint64_optimal len);
  let x = R.String ty len l in
  R.valid_eq R.basic_data_model x;
  R.mk_cbor_eq x;
  R.mk_det_raw_cbor_mk_cbor x;
  RF.serialize_cbor_string_length_gt ty len l;
  ()

let cbor_det_serialize_map m =
  RF.serialize_cbor_map (R.mk_det_raw_cbor_map_raw m)

let cbor_det_serialize_map_empty () =
  RF.serialize_cbor_map_nil ()

let cbor_det_serialize_map_singleton key value =
  R.mk_det_raw_cbor_map_raw_singleton key value;
  RF.serialize_cbor_map_singleton (R.mk_det_raw_cbor key) (R.mk_det_raw_cbor value)

#push-options "--z3rlimit 32"

#restart-solver

let rec cbor_det_serialize_map_length_union_disjoint_eq
  (m1: cbor_map)
  (l2: list (cbor & cbor))
  (m2: cbor_map)
: Lemma
  (requires (
    List.Tot.length l2 == cbor_map_length m2 /\
    List.Tot.no_repeats_p (List.Tot.map fst l2) /\
    (forall x . List.Tot.assoc x l2 == cbor_map_get m2 x) /\
    cbor_map_disjoint m1 m2
  ))
  (ensures (
    Seq.length (cbor_det_serialize_map (cbor_map_union m1 m2)) == Seq.length (cbor_det_serialize_map m1) + Seq.length (RF.serialize_cbor_map (List.Tot.map R.mk_det_raw_cbor_map_entry l2))
  ))
  (decreases l2)
= match l2 with
  | [] ->
    RF.serialize_cbor_map_nil ();
    assert (cbor_map_equal m2 cbor_map_empty)
  | (k, v) :: q ->
    let ms = cbor_map_singleton k v in
    let m1' = cbor_map_union m1 ms in
    let m2' = cbor_map_sub m2 ms in
    assert (cbor_map_equal (cbor_map_union m1 m2) (cbor_map_union m1' m2'));
    RF.serialize_cbor_map_cons (R.mk_det_raw_cbor k) (R.mk_det_raw_cbor v) (List.Tot.map R.mk_det_raw_cbor_map_entry q);
    List.Tot.assoc_mem k q;
    assert (cbor_map_equal m2 (cbor_map_union m2' ms));
    cbor_map_length_disjoint_union m2' ms;
    cbor_map_length_singleton k v;
    let kr = R.mk_det_raw_cbor k in
    let vr = R.mk_det_raw_cbor v in
    assert (RF.serialize_cbor_map (List.Tot.map R.mk_det_raw_cbor_map_entry l2) == (RF.serialize_cbor kr `Seq.append` RF.serialize_cbor vr) `Seq.append` RF.serialize_cbor_map (List.Tot.map R.mk_det_raw_cbor_map_entry q)
    );
    assert (Seq.length (RF.serialize_cbor_map (List.Tot.map R.mk_det_raw_cbor_map_entry l2)) == Seq.length (RF.serialize_cbor kr) + Seq.length (RF.serialize_cbor vr) + Seq.length (RF.serialize_cbor_map (List.Tot.map R.mk_det_raw_cbor_map_entry q))
    );
    cbor_det_serialize_map_length_union_disjoint_eq m1' q m2';
    R.mk_det_raw_cbor_map_raw_snoc m1 k v;
    let l1 = R.mk_det_raw_cbor_map_raw m1 in
    let kv = (R.mk_det_raw_cbor k, R.mk_det_raw_cbor v) in
    R.mk_det_raw_cbor_map_raw_assoc m1 k;
    R.list_setoid_assoc_sorted_optimal RF.deterministically_encoded_cbor_map_key_order (R.mk_det_raw_cbor k) l1;
    List.Tot.assoc_mem (R.mk_det_raw_cbor k) l1;
    RF.cbor_map_insert_sorted l1 kv;
    RF.serialize_cbor_map_insert_length l1 kv;
    assert (Some? (RF.cbor_map_insert l1 kv));
    let Some l1' = RF.cbor_map_insert l1 kv in
    assert (cbor_det_serialize_map m1' == RF.serialize_cbor_map l1');
    ()

#pop-options

let cbor_det_serialize_map_length_eq
  (l2: list (cbor & cbor))
  (m2: cbor_map)
: Lemma
  (requires (
    List.Tot.length l2 == cbor_map_length m2 /\
    List.Tot.no_repeats_p (List.Tot.map fst l2) /\
    (forall x . List.Tot.assoc x l2 == cbor_map_get m2 x)
  ))
  (ensures (
    Seq.length (cbor_det_serialize_map (m2)) == Seq.length (RF.serialize_cbor_map (List.Tot.map R.mk_det_raw_cbor_map_entry l2))
  ))
= cbor_det_serialize_map_length_union_disjoint_eq cbor_map_empty l2 m2;
  cbor_det_serialize_map_empty ()

let rec cbor_map_to_list
  (m: cbor_map)
  (l: list cbor)
: Tot (list (cbor & cbor))
= match l with
  | [] -> []
  | k :: q ->
    begin match cbor_map_get m k with
    | None -> cbor_map_to_list m q
    | Some v -> (k, v) :: cbor_map_to_list m q
    end

let rec cbor_map_to_list_map_fst
  (m: cbor_map)
  (l: list cbor)
: Lemma
  (requires (
    forall x . List.Tot.memP x l ==> cbor_map_defined x m
  ))
  (ensures (
    let l' = cbor_map_to_list m l in
    List.Tot.map fst l' == l
  ))
= match l with
  | [] -> ()
  | _ :: q -> cbor_map_to_list_map_fst m q

let rec cbor_map_to_list_assoc
  (m: cbor_map)
  (l: list cbor)
  (k: cbor)
: Lemma
  (requires (
    List.Tot.memP k l /\
    cbor_map_defined k m
  ))
  (ensures (
    let l' = cbor_map_to_list m l in
    List.Tot.assoc k l' == cbor_map_get m k
  ))
= match l with
  | [] -> ()
  | k' :: q ->
    if k = k'
    then ()
    else cbor_map_to_list_assoc m q k

let cbor_map_to_list_assoc'
  (m: cbor_map)
  (l: list cbor)
  (k: cbor)
: Lemma
  (ensures (
    List.Tot.memP k l /\
    cbor_map_defined k m
  ) ==> (
    let l' = cbor_map_to_list m l in
    List.Tot.assoc k l' == cbor_map_get m k
  ))
= Classical.move_requires (cbor_map_to_list_assoc m l) k

let cbor_map_to_list_correct
  (m: cbor_map)
  (l: list cbor)
: Lemma
  (requires (
    (forall x . List.Tot.memP x l <==> cbor_map_defined x m) /\
    List.Tot.no_repeats_p l
  ))
  (ensures (
    let l' = cbor_map_to_list m l in
    (forall x . List.Tot.assoc x l' == cbor_map_get m x)
  ))
= let l' = cbor_map_to_list m l in
  Classical.forall_intro (cbor_map_to_list_assoc' m l);
  cbor_map_to_list_map_fst m l;
  Classical.forall_intro (fun x -> List.Tot.assoc_mem x l')

let cbor_det_serialize_map_append_length m1 m2 =
  let l = cbor_map_key_list m2 in
  let l' = cbor_map_to_list m2 l in
  cbor_map_to_list_map_fst m2 l;
  cbor_map_to_list_correct m2 l;
  cbor_det_serialize_map_length_union_disjoint_eq m1 l' m2;
  cbor_det_serialize_map_length_eq l' m2

let cbor_det_serialize_map_length_gt_list l =
  R.mk_cbor_eq_map (pack (CMap l));
  RF.cbor_serialize_map_length_gt_list (R.mk_raw_uint64 (U64.uint_to_t (cbor_map_length l))) (R.mk_det_raw_cbor_map_raw l);
  ()
