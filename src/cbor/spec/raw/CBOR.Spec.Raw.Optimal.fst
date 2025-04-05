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

