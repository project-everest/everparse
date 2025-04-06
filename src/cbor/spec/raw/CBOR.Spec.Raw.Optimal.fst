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

(*
let raw_data_item_uint64_optimize_valid (x: raw_data_item) : Lemma
    (requires (valid basic_data_model x == true))
    (ensures (valid basic_data_model (raw_data_item_uint64_optimize x) == true))
    (decreases x)
= valid_eq' basic_data_model x;
  valid_eq' basic_data_model (raw_data_item_uint64_optimize x);
  holds_on_raw_data_item_fmap_inv
    raw_data_item_uint64_optimize_elem
    (valid_item basic_data_model)
    (fun x ->
      match x with
      | Map len v ->
        assert_norm (raw_data_item_uint64_optimize == raw_data_item_fmap raw_data_item_uint64_optimize_elem);
        let v' = List.Tot.map (apply_on_pair raw_data_item_uint64_optimize) v in
        assert (pre_holds_on_raw_data_item (valid_item basic_data_model) (pre_raw_data_item_fmap raw_data_item_uint64_optimize_elem x) == true);
        assert (List.Tot.for_all (holds_on_pair (holds_on_raw_data_item (valid_item basic_data_model))) v');
        assert (pre_raw_data_item_fmap raw_data_item_uint64_optimize_elem x == Map len v' );
        valid_raw_data_item_map_fmap_equiv basic_data_model raw_data_item_uint64_optimize_elem v (fun x -> raw_data_item_uint64_optimize_elem_equiv x);
        assert (valid_item basic_data_model (pre_raw_data_item_fmap raw_data_item_uint64_optimize_elem x));
        assume False
      | _ -> ()
    )
    (fun x ->
       valid_eq' basic_data_model x;
       valid_eq' basic_data_model (raw_data_item_uint64_optimize x);
       raw_data_item_uint64_optimize_elem_valid x
    )
    x


(*
let raw_data_item_uint64_optimize_equiv (x: raw_data_item) : Lemma
  (requires (valid basic_data_model x == true))
  (ensures (raw_equiv2 x (raw_data_item_uint64_optimize x) == true))
= raw_equiv2_fmap raw_data_item_uint64_optimize_elem raw_data_item_uint64_optimize_elem_equiv x
