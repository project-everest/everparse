module CBOR.Spec.Raw.Valid
include CBOR.Spec.Raw.Base
open CBOR.Spec.Util
open FStar.Mul

module U8 = FStar.UInt8
module U64 = FStar.UInt64

noextract
let map_entry_order
  (#key: Type)
  (key_order: (key -> key -> bool))
  (value: Type)
  (m1: (key & value))
  (m2: (key & value))
: Tot bool
= key_order (fst m1) (fst m2)

let valid_raw_data_item_map
  (v: list (raw_data_item & raw_data_item))
: Tot bool
= list_no_setoid_repeats (map_entry_order raw_equiv _) v

let valid_raw_data_item_map_no_repeats
  (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires (valid_raw_data_item_map v == true))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst v)))
= list_no_setoid_repeats_map
    fst
    v
    (map_entry_order raw_equiv _)
    raw_equiv
    (fun x x' -> ());
  list_no_setoid_repeats_implies
    raw_equiv
    ( = )
    (List.Tot.map fst v)
    (fun x x' -> raw_equiv_refl x);
  list_no_setoid_repeats_no_repeats (List.Tot.map fst v)

let valid_raw_data_item_elem
  (l: raw_data_item)
: Tot bool
= match l with
  | Map _ v -> valid_raw_data_item_map v
  | _ -> true

let valid_raw_data_item
  (l: raw_data_item)
: Tot bool
= holds_on_raw_data_item valid_raw_data_item_elem l

(* Shortest-size integers *)

let raw_uint64_optimal (x: raw_uint64) : Tot bool =
  ((U64.v x.value <= U8.v max_simple_value_additional_info) = (x.size = 0)) &&
  begin
    if x.size <= 1
    then true
    else pow2 (8 * pow2 (x.size - 2)) <= U64.v x.value
  end

let raw_uint64_optimal_unique (x1 x2: raw_uint64) : Lemma
  (requires (raw_uint64_optimal x1 /\ raw_uint64_optimal x2 /\ raw_uint64_equiv x1 x2))
  (ensures (x1 == x2))
= ()

let rec raw_uint64_optimize (x: raw_uint64) : Pure raw_uint64
  (requires True)
  (ensures (fun x' -> raw_uint64_equiv x x' /\ raw_uint64_optimal x'))
  (decreases x.size)
= if U64.v x.value <= U8.v max_simple_value_additional_info
  then { x with size = 0 }
  else if x.size <= 1
  then x
  else if pow2 (8 * pow2 (x.size - 2)) <= U64.v x.value
  then x
  else raw_uint64_optimize { x with size = x.size - 1 }

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

let raw_data_item_uint64_optimize_elem_correct (x: raw_data_item) : Lemma
  (raw_data_item_ints_optimal_elem (raw_data_item_uint64_optimize_elem x) == true)
= ()

let raw_data_item_uint64_optimize_elem_equiv (x: raw_data_item) : Lemma
  (raw_equiv x (raw_data_item_uint64_optimize_elem x) == true)
= raw_equiv_eq x (raw_data_item_uint64_optimize_elem x);
  match x with
  | Array _ v -> list_for_all2_refl raw_equiv v (fun x -> raw_equiv_refl x)
  | Map _ v ->
    list_for_all2_refl (holds_on_pair2 raw_equiv) v (fun x -> raw_equiv_refl (fst x); raw_equiv_refl (snd x));
    list_for_all2_exists (holds_on_pair2 raw_equiv) v v
  | Tagged _ v -> raw_equiv_refl v
  | _ -> ()

let raw_data_item_uint64_optimize_elem_valid (x: raw_data_item) : Lemma
  (requires (valid_raw_data_item x == true))
  (ensures (valid_raw_data_item (raw_data_item_uint64_optimize_elem x) == true))
= holds_on_raw_data_item_eq valid_raw_data_item_elem x;
  holds_on_raw_data_item_eq valid_raw_data_item_elem (raw_data_item_uint64_optimize_elem x)

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

let rec raw_data_item_uint64_optimize_correct (x: raw_data_item) : Lemma
  (ensures (raw_data_item_ints_optimal (raw_data_item_uint64_optimize x) == true))
  (decreases x)
= holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x;
  raw_data_item_fmap_eq raw_data_item_uint64_optimize_elem x;
  assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
  assert_norm (raw_data_item_uint64_optimize == raw_data_item_fmap raw_data_item_uint64_optimize_elem);
  match x with
  | Map len v ->
    list_for_all_truep v;
    list_for_all_map (apply_on_pair raw_data_item_uint64_optimize) v truep (holds_on_pair raw_data_item_ints_optimal) (fun x ->
      raw_data_item_uint64_optimize_correct (fst x);
      raw_data_item_uint64_optimize_correct (snd x)
    )
  | Array len v ->
    list_for_all_truep v;
    list_for_all_map (raw_data_item_uint64_optimize) v truep raw_data_item_ints_optimal (fun x ->
      raw_data_item_uint64_optimize_correct x
    )
  | Tagged len v -> raw_data_item_uint64_optimize_correct v
  | _ -> ()

let rec raw_data_item_uint64_optimize_equiv (x: raw_data_item) : Lemma
  (ensures (raw_equiv x (raw_data_item_uint64_optimize x) == true))
  (decreases x)
= raw_data_item_fmap_eq raw_data_item_uint64_optimize_elem x;
  assert_norm (raw_data_item_uint64_optimize == raw_data_item_fmap raw_data_item_uint64_optimize_elem);
  let x' = raw_data_item_uint64_optimize x in
  raw_equiv_eq x x';
  match x with
  | Map len v ->
    list_for_all2_map (apply_on_pair raw_data_item_uint64_optimize) v (holds_on_pair2 raw_equiv) (fun x ->
      raw_data_item_uint64_optimize_equiv (fst x);
      raw_data_item_uint64_optimize_equiv (snd x)
    );
    let v_ = List.Tot.map (apply_on_pair raw_data_item_uint64_optimize) v in
    list_for_all2_exists (holds_on_pair2 raw_equiv) v v_;
    list_for_all2_swap (holds_on_pair2 raw_equiv) v v_;
    list_for_all2_implies (swap (holds_on_pair2 raw_equiv)) (holds_on_pair2 raw_equiv) v_ v (fun x x_ ->
      raw_equiv_sym (fst x) (fst x_);
      raw_equiv_sym (snd x) (snd x_)
    );
    list_for_all2_exists (holds_on_pair2 raw_equiv) v_ v;
    let x_ = Map len v_ in
    raw_equiv_eq x x_;
    raw_data_item_uint64_optimize_elem_equiv x_;
    raw_equiv_trans x x_ x'
  | Array len v ->
    list_for_all2_map raw_data_item_uint64_optimize v raw_equiv (fun x ->
      raw_data_item_uint64_optimize_equiv x
    );
    let x_ = Array len (List.Tot.map raw_data_item_uint64_optimize v) in
    raw_equiv_eq x x_;
    raw_data_item_uint64_optimize_elem_equiv x_;
    raw_equiv_trans x x_ x'
  | Tagged len v ->
    raw_data_item_uint64_optimize_equiv v;
    let x_ = Tagged len (raw_data_item_uint64_optimize v) in
    raw_equiv_eq x x_;
    raw_data_item_uint64_optimize_elem_equiv x_;
    raw_equiv_trans x x_ x'
  | _ -> raw_data_item_uint64_optimize_elem_equiv x

(* Sorting map keys *)

noextract
let raw_data_item_sorted_elem (order: (raw_data_item -> raw_data_item -> bool)) (x: raw_data_item) : Tot bool
= match x with
  | Map _ l ->
      FStar.List.Tot.sorted (map_entry_order order _) l
  | _ -> true

noextract
let raw_data_item_sorted (order: (raw_data_item -> raw_data_item -> bool)) : Tot (raw_data_item -> bool)
= holds_on_raw_data_item (raw_data_item_sorted_elem order)

(* Correctness of the (old, new or other) deterministic map key orders wrt. validity *)

val raw_equiv_sorted_optimal
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

val raw_data_item_sorted_optimal_valid
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

let rec raw_equiv_list_no_map
  (l1 l2: list raw_data_item)
: Tot bool
  (decreases (list_sum raw_data_item_size l1))
= match l1, l2 with
  | [], [] -> true
  | x1 :: q1, x2 :: q2 ->
    raw_data_item_size_eq x1;
    begin match x1, x2 with
    | Simple v1, Simple v2 -> v1 = v2 && raw_equiv_list_no_map q1 q2
    | Int64 ty1 v1, Int64 ty2 v2 -> ty1 = ty2 && raw_uint64_equiv v1 v2 && raw_equiv_list_no_map q1 q2
    | String ty1 len1 v1, String ty2 len2 v2 -> ty1 = ty2 && raw_uint64_equiv len1 len2 && v1 = v2 && raw_equiv_list_no_map q1 q2
    | Array len1 v1, Array len2 v2 ->
      list_sum_append raw_data_item_size v1 q1;
      raw_uint64_equiv len1 len2 &&
      raw_equiv_list_no_map (List.Tot.append v1 q1) (List.Tot.append v2 q2)
    | Tagged tag1 v1, Tagged tag2 v2 ->
      raw_uint64_equiv tag1 tag2 &&
      raw_equiv_list_no_map (v1 :: q1) (v2 :: q2)
    | _ -> false
    end
  | _ -> false

val raw_equiv_list_no_map_append
  (ll1 lr1 ll2 lr2: list raw_data_item)
: Lemma
  (requires (List.Tot.length ll1 == List.Tot.length ll2))
  (ensures (raw_equiv_list_no_map (List.Tot.append ll1 lr1) (List.Tot.append ll2 lr2) == (raw_equiv_list_no_map ll1 ll2 && raw_equiv_list_no_map lr1 lr2)))

val raw_equiv_list_no_map_no_map
  (l1 l2: list raw_data_item)
: Lemma
  (requires (raw_equiv_list_no_map l1 l2 == true))
  (ensures (List.Tot.for_all (holds_on_raw_data_item (notp Map?)) l1 == true))

val raw_equiv_list_no_map_equiv
  (l1 l2: list raw_data_item)
: Lemma
  (requires (raw_equiv_list_no_map l1 l2 == true))
  (ensures (list_for_all2 raw_equiv l1 l2 == true))

val raw_equiv_list_no_map_sym
  (l1 l2: list raw_data_item)
: Lemma
  (raw_equiv_list_no_map l1 l2 == raw_equiv_list_no_map l2 l1)

val raw_equiv_equiv_list_no_map
  (l1 l2: list raw_data_item)
: Lemma
  (requires (
    list_for_all2 raw_equiv l1 l2 == true /\
    list_for_all2 (prod_or (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?))) l1 l2 == true
  ))
  (ensures (
    raw_equiv_list_no_map l1 l2 == true
  ))

val raw_equiv_list_no_map_eq
  (l1 l2: list raw_data_item)
: Lemma
  (raw_equiv_list_no_map l1 l2 == (list_for_all2 raw_equiv l1 l2 && list_for_all2 (prod_or (holds_on_raw_data_item (notp Map?)) (holds_on_raw_data_item (notp Map?))) l1 l2))

let raw_equiv_no_map
  (x1 x2: raw_data_item)
: Tot bool
= raw_equiv_list_no_map [x1] [x2]

let raw_equiv_list_no_map_no_map2
  (l1 l2: list raw_data_item)
: Lemma
  (requires (raw_equiv_list_no_map l1 l2 == true))
  (ensures (List.Tot.for_all (holds_on_raw_data_item (notp Map?)) l1 == true /\
    List.Tot.for_all (holds_on_raw_data_item (notp Map?)) l2 == true
  ))
= raw_equiv_list_no_map_no_map l1 l2;
  raw_equiv_list_no_map_sym l1 l2;
  raw_equiv_list_no_map_no_map l2 l1

val raw_equiv_list_no_map_eq'
  (l1 l2: list raw_data_item)
: Lemma
  (ensures (raw_equiv_list_no_map l1 l2 == list_for_all2 raw_equiv_no_map l1 l2))

let no_maps_in_keys_map
  (v: list (raw_data_item & raw_data_item))
: Tot bool
= List.Tot.for_all (holds_on_raw_data_item (notp Map?)) (List.Tot.map fst v)

let no_maps_in_keys_elem
  (l: raw_data_item)
: Tot bool
= match l with
  | Map _ v -> no_maps_in_keys_map v
  | _ -> true

let no_maps_in_keys = holds_on_raw_data_item no_maps_in_keys_elem


let valid_raw_data_item_no_maps_in_keys_map
  (v: list (raw_data_item & raw_data_item))
: Tot bool
= list_no_setoid_repeats (map_entry_order raw_equiv_no_map _) v

let valid_raw_data_item_no_maps_in_keys_elem_gen
  (p: raw_data_item -> bool)
  (l: raw_data_item)
: Tot bool
= p l &&
  begin match l with
  | Map _ v -> valid_raw_data_item_no_maps_in_keys_map v
  | _ -> true
  end

let valid_raw_data_item_no_maps_in_keys_elem =
  valid_raw_data_item_no_maps_in_keys_elem_gen no_maps_in_keys_elem

let valid_raw_data_item_no_maps_in_keys_gen
  (p: raw_data_item -> bool)
: Tot (raw_data_item -> bool)
= holds_on_raw_data_item (valid_raw_data_item_no_maps_in_keys_elem_gen p)

let valid_raw_data_item_no_maps_in_keys = holds_on_raw_data_item valid_raw_data_item_no_maps_in_keys_elem

val valid_no_maps_in_keys_no_maps_in_keys_gen
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item_no_maps_in_keys_gen p x == true))
  (ensures (holds_on_raw_data_item p x == true))

let valid_no_maps_in_keys_no_maps_in_keys
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item_no_maps_in_keys x == true))
  (ensures (no_maps_in_keys x == true))
= assert_norm (valid_raw_data_item_no_maps_in_keys == valid_raw_data_item_no_maps_in_keys_gen no_maps_in_keys_elem);
  valid_no_maps_in_keys_no_maps_in_keys_gen no_maps_in_keys_elem x

val valid_no_maps_in_keys_valid_map
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

val valid_no_maps_in_keys_valid
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item_no_maps_in_keys x == true))
  (ensures (valid_raw_data_item x == true))

val valid_no_maps_in_keys_valid_gen
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (
    valid_raw_data_item_no_maps_in_keys_gen p x == true /\
    (forall x' . p x' == true ==> no_maps_in_keys_elem x' == true)
  ))
  (ensures (valid_raw_data_item x == true))

val valid_valid_no_maps_in_keys_gen
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item x == true /\
    holds_on_raw_data_item p x == true
  ))
  (ensures (valid_raw_data_item_no_maps_in_keys_gen p x == true))

val valid_valid_no_maps_in_keys
  (x: raw_data_item)
: Lemma
  (requires (valid_raw_data_item x == true /\
    no_maps_in_keys x == true
  ))
  (ensures (valid_raw_data_item_no_maps_in_keys x == true))

val valid_raw_data_item_no_maps_in_keys_eq
  (x: raw_data_item)
: Lemma
  (valid_raw_data_item_no_maps_in_keys x ==
    (valid_raw_data_item x && no_maps_in_keys x)
  )

val valid_raw_data_item_no_maps_in_keys_gen_eq
  (p: raw_data_item -> bool)
  (x: raw_data_item)
: Lemma
  (requires (
    forall x' . p x' == true ==> no_maps_in_keys_elem x' == true
  ))
  (ensures (valid_raw_data_item_no_maps_in_keys_gen p x ==
    (valid_raw_data_item x && holds_on_raw_data_item p x)
  ))

