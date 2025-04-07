module CBOR.Spec.Raw.Optimal
include CBOR.Spec.Raw.Valid2
open CBOR.Spec.Util
open FStar.Mul

module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* Shortest-size integers *)

let raw_uint64_optimal (x: raw_uint64) : Tot bool =
  ((U64.v x.value <= U8.v max_simple_value_additional_info) = (U8.v x.size = 0)) &&
  begin
    if U8.v x.size <= 1
    then true
    else pow2 (8 * pow2 (U8.v x.size - 2)) <= U64.v x.value
  end

let raw_uint64_optimal_unique (x1 x2: raw_uint64) : Lemma
  (requires (raw_uint64_optimal x1 /\ raw_uint64_optimal x2 /\ raw_uint64_equiv x1 x2))
  (ensures (x1 == x2))
= ()

let mk_raw_uint64 (x: U64.t) : Pure raw_uint64
  (requires True)
  (ensures (fun y -> y.value == x /\
    raw_uint64_optimal y == true
  ))
= let size =
    if U64.lte x (FStar.Int.Cast.uint8_to_uint64 max_simple_value_additional_info)
    then 0uy
    else if U64.lt x 256uL
    then 1uy
    else if U64.lt x 65536uL
    then 2uy
    else if U64.lt x 4294967296uL
    then 3uy
    else 4uy
  in
  { size = size; value = x }

let raw_uint64_optimize (x: raw_uint64) : Pure raw_uint64
  (requires True)
  (ensures (fun x' -> raw_uint64_equiv x x' /\ raw_uint64_optimal x'))
= mk_raw_uint64 x.value

let raw_data_item_ints_optimal_elem (x: raw_data_item) : Tot bool =
  match x with
  | Int64 _ v
  | String _ v _
  | Array v _
  | Map v _
  | Tagged v _
    -> raw_uint64_optimal v
  | Simple _ -> true

let raw_data_item_ints_optimal : raw_data_item -> Tot bool =
  holds_on_raw_data_item raw_data_item_ints_optimal_elem

let raw_data_item_uint64_optimize_elem (x: raw_data_item) : Tot raw_data_item =
  match x with
  | Int64 ty v -> Int64 ty (raw_uint64_optimize v)
  | String ty len v -> String ty (raw_uint64_optimize len) v
  | Array len v -> Array (raw_uint64_optimize len) v
  | Map len v -> Map (raw_uint64_optimize len) v
  | Tagged tag v -> Tagged (raw_uint64_optimize tag) v
  | _ -> x

let raw_data_item_uint64_optimize_elem_valid (x: raw_data_item) : Lemma
  (requires (valid basic_data_model x == true))
  (ensures (valid basic_data_model (raw_data_item_uint64_optimize_elem x) == true /\
    raw_equiv2 x (raw_data_item_uint64_optimize_elem x) == true
  ))
= valid_eq basic_data_model x;
  valid_eq basic_data_model (raw_data_item_uint64_optimize_elem x);
  equiv_eq basic_data_model x (raw_data_item_uint64_optimize_elem x);
  match x with
  | Array _ v ->
    list_for_all2_refl raw_equiv2 v (fun x -> equiv_refl basic_data_model x)
  | Map _ v ->
    equiv_refl_forall basic_data_model;
    equiv_sym_forall basic_data_model;
    equiv_trans_forall basic_data_model;
    list_setoid_assoc_eq_refl raw_equiv2 raw_equiv2 v;
    ()
  | Tagged _ v -> equiv_refl basic_data_model v
  | _ -> ()

let raw_data_item_uint64_optimize_elem_equiv (x: raw_data_item) : Lemma
  (requires (valid basic_data_model x == true))
  (ensures (raw_equiv2 x (raw_data_item_uint64_optimize_elem x) == true))
= equiv_eq basic_data_model x (raw_data_item_uint64_optimize_elem x);
  raw_data_item_uint64_optimize_elem_valid x;
  ()

let raw_data_item_uint64_optimize_elem_size (x: raw_data_item) : Lemma
  (raw_data_item_size (raw_data_item_uint64_optimize_elem x) == raw_data_item_size x)
= raw_data_item_size_eq x;
  raw_data_item_size_eq (raw_data_item_uint64_optimize_elem x)

unfold
let raw_data_item_uint64_optimize : raw_data_item -> raw_data_item =
  raw_data_item_fmap raw_data_item_uint64_optimize_elem

let rec raw_data_item_uint64_optimize_size (x: raw_data_item) : Lemma
  (ensures (raw_data_item_size (raw_data_item_uint64_optimize x) == raw_data_item_size x))
  (decreases x)
= raw_data_item_size_eq x;
  raw_data_item_size_eq (raw_data_item_uint64_optimize x);
  raw_data_item_fmap_eq raw_data_item_uint64_optimize_elem x;
  assert_norm (raw_data_item_uint64_optimize == raw_data_item_fmap raw_data_item_uint64_optimize_elem);
  match x with
  | Map len v ->
    assert (raw_data_item_uint64_optimize (Map len v) == raw_data_item_fmap raw_data_item_uint64_optimize_elem (Map len v));
    assert (raw_data_item_uint64_optimize (Map len v) == raw_data_item_uint64_optimize_elem (Map len (List.Tot.map (apply_on_pair raw_data_item_uint64_optimize) v)));
    list_sum_map (pair_sum raw_data_item_size raw_data_item_size) v (pair_sum raw_data_item_size raw_data_item_size) (apply_on_pair raw_data_item_uint64_optimize) (fun x ->
      raw_data_item_uint64_optimize_size (fst x);
      raw_data_item_uint64_optimize_size (snd x)
    );
    raw_data_item_uint64_optimize_elem_size (Map len (List.Tot.map (apply_on_pair raw_data_item_uint64_optimize) v))
  | Array len v ->
    list_sum_map raw_data_item_size v raw_data_item_size raw_data_item_uint64_optimize (fun x ->
      raw_data_item_uint64_optimize_size x
    );
    raw_data_item_uint64_optimize_elem_size (Array len (List.Tot.map raw_data_item_uint64_optimize v))
  | Tagged len v ->
    raw_data_item_uint64_optimize_size v;
    raw_data_item_uint64_optimize_elem_size (Tagged len (raw_data_item_uint64_optimize v))
  | _ -> raw_data_item_uint64_optimize_elem_size x

let raw_data_item_uint64_optimize_correct (x: raw_data_item) : Lemma
  (ensures (raw_data_item_ints_optimal (raw_data_item_uint64_optimize x) == true))
= holds_on_raw_data_item_fmap raw_data_item_uint64_optimize_elem raw_data_item_ints_optimal_elem (fun _ -> ()) x

let rec raw_data_item_uint64_optimize_valid (x: raw_data_item) (sq: squash (valid basic_data_model x)) : Lemma
    (ensures (valid basic_data_model (raw_data_item_uint64_optimize x) /\
      equiv basic_data_model x (raw_data_item_uint64_optimize x)
    ))
    (decreases (raw_data_item_size x))
= let x' = (raw_data_item_uint64_optimize x) in
  valid_eq basic_data_model x;
  valid_eq basic_data_model x';
  equiv_eq basic_data_model x x';
  raw_data_item_fmap_eq raw_data_item_uint64_optimize_elem x;
  raw_data_item_size_eq x;
  raw_data_item_size_eq x';
  equiv_refl_forall basic_data_model;
  equiv_sym_forall basic_data_model;
  equiv_trans_forall basic_data_model;
  match x with
  | Tagged _ v ->
    raw_data_item_uint64_optimize_valid v ()
  | Array _ v ->
    let v' = (List.Tot.map raw_data_item_uint64_optimize v) in
    List.Tot.for_all_mem (valid basic_data_model) v;
    list_for_all_intro
      (valid basic_data_model)
      v'
      (fun x ->
        let x' : raw_data_item = x in
        let x0 = list_memP_map_elim raw_data_item_uint64_optimize x' v in
        list_sum_memP raw_data_item_size v x0;
        raw_data_item_uint64_optimize_valid x0 ();
        ()
      );
    list_for_all2_map
      raw_data_item_uint64_optimize
      v
      (equiv basic_data_model)
      (fun x ->
        list_sum_memP raw_data_item_size v x;
        raw_data_item_uint64_optimize_valid x ();
        ()
      );
    ()
  | Map _ v ->
    let v' = List.Tot.map (apply_on_pair raw_data_item_uint64_optimize) v in
    List.Tot.for_all_mem (valid basic_data_model) (List.Tot.map fst v);
    List.Tot.for_all_mem (valid basic_data_model) (List.Tot.map snd v);
    list_map_fst_apply_on_pair raw_data_item_uint64_optimize v;
    list_map_snd_apply_on_pair raw_data_item_uint64_optimize v;
    list_for_all_intro
      (valid basic_data_model)
      (List.Tot.map fst v')
      (fun z ->
        let z_ : raw_data_item = z in
        assert (List.Tot.memP z_ (List.Tot.map fst v'));
        assert (List.Tot.memP z_ (List.Tot.map raw_data_item_uint64_optimize (List.Tot.map fst v)));
        let z0 = list_memP_map_elim raw_data_item_uint64_optimize z_ (List.Tot.map fst v) in
        let z1 = list_memP_map_elim fst z0 v in
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v z1;
        assert (z0 == fst z1);
        assert (valid basic_data_model z0);
        assert (raw_data_item_size z0 < raw_data_item_size x);
        raw_data_item_uint64_optimize_valid z0 ();
        ()
      );
    list_for_all_intro
      (valid basic_data_model)
      (List.Tot.map snd v')
      (fun z ->
        let z_ : raw_data_item = z in
        assert (List.Tot.memP z_ (List.Tot.map snd v'));
        assert (List.Tot.memP z_ (List.Tot.map raw_data_item_uint64_optimize (List.Tot.map snd v)));
        let z0 = list_memP_map_elim raw_data_item_uint64_optimize z_ (List.Tot.map snd v) in
        let z1 = list_memP_map_elim snd z0 v in
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v z1;
        assert (z0 == snd z1);
        assert (valid basic_data_model z0);
        assert (raw_data_item_size z0 < raw_data_item_size x);
        raw_data_item_uint64_optimize_valid z0 ();
        ()
      );
    list_no_setoid_repeats_map
      raw_data_item_uint64_optimize
      (List.Tot.map fst v)
      (equiv basic_data_model)
      (equiv basic_data_model)
      (fun z z' ->
        let z_ : raw_data_item = z in
        let z'_ : raw_data_item = z' in
        let z0 = list_memP_map_elim fst z_ v in
        let z0' = list_memP_map_elim fst z'_ v in
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v z0;
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v z0';
        raw_data_item_uint64_optimize_valid z_ ();
        raw_data_item_uint64_optimize_valid z'_ ();
        ()
      );
    assert (valid basic_data_model x');
    list_for_all2_map raw_data_item_uint64_optimize (List.Tot.map fst v) (equiv basic_data_model) (fun z ->
      let z_ : raw_data_item = z in
      let z0 = list_memP_map_elim fst z_ v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v z0;
      raw_data_item_uint64_optimize_valid z_ ();
      ()
    );
    list_for_all2_map raw_data_item_uint64_optimize (List.Tot.map snd v) (equiv basic_data_model) (fun z ->
      let z_ : raw_data_item = z in
      let z0 = list_memP_map_elim snd z_ v in
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) v z0;
      raw_data_item_uint64_optimize_valid z_ ();
      ()
    );
    list_setoid_assoc_eq_refl
      (equiv basic_data_model)
      (equiv basic_data_model)
      v;
    list_setoid_assoc_eq_equiv1 
      (equiv basic_data_model)
      (equiv basic_data_model)
      v v' v;
    list_setoid_assoc_eq_equiv2
      (equiv basic_data_model)
      (equiv basic_data_model)
      v v v';
    assert (equiv basic_data_model x x');
    ()
  | _ -> ()
