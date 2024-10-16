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
= holds_on_raw_data_item valid_raw_data_item_elem

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

let raw_data_item_uint64_optimize_correct (x: raw_data_item) : Lemma
  (ensures (raw_data_item_ints_optimal (raw_data_item_uint64_optimize x) == true))
= holds_on_raw_data_item_fmap raw_data_item_uint64_optimize_elem raw_data_item_ints_optimal_elem (fun _ -> ()) x

let raw_data_item_uint64_optimize_equiv (x: raw_data_item) : Lemma
  (ensures (raw_equiv x (raw_data_item_uint64_optimize x) == true))
= raw_equiv_fmap raw_data_item_uint64_optimize_elem raw_data_item_uint64_optimize_elem_equiv x

let valid_raw_data_item_map_fmap_equiv
  (f: raw_data_item -> raw_data_item)
  (prf: (x: raw_data_item) -> Lemma
    (raw_equiv x (f x) == true)
  )
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (valid_raw_data_item_map l == true))
  (ensures (valid_raw_data_item_map (List.Tot.map (apply_on_pair f) l) == true))
= 
        list_no_setoid_repeats_map (apply_on_pair f) l (map_entry_order raw_equiv _) (map_entry_order raw_equiv _) (fun x x' ->
          prf (fst x);
          prf (fst x');
          raw_equiv_sym (f (fst x')) (fst x');
          raw_equiv_trans (fst x) (f (fst x)) (f (fst x'));
          raw_equiv_trans (fst x) (f (fst x')) (fst x')
        )

let raw_data_item_uint64_optimize_valid (x: raw_data_item) : Lemma
    (requires (valid_raw_data_item x == true))
    (ensures (valid_raw_data_item (raw_data_item_uint64_optimize x) == true))
= holds_on_raw_data_item_fmap_inv
    raw_data_item_uint64_optimize_elem
    valid_raw_data_item_elem
    (fun x ->
      match x with
      | Map len v ->
        assert_norm (raw_data_item_uint64_optimize == raw_data_item_fmap raw_data_item_uint64_optimize_elem);
        valid_raw_data_item_map_fmap_equiv raw_data_item_uint64_optimize (fun x -> raw_data_item_uint64_optimize_equiv x) v
      | _ -> ()
    )
    (fun x -> raw_data_item_uint64_optimize_elem_valid x)
    x

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

let raw_equiv_sorted_optimal_eq
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (x1 x2: raw_data_item)
: Lemma
  (requires (
    raw_data_item_sorted order x1 /\
    raw_data_item_sorted order x2 /\
    raw_data_item_ints_optimal x1 /\
    raw_data_item_ints_optimal x2
  ))
  (ensures (raw_equiv x1 x2 == (x1 = x2)))
= if raw_equiv x1 x2
  then raw_equiv_sorted_optimal order x1 x2
  else if x1 = x2
  then raw_equiv_refl x1
  else ()

let valid_raw_data_item_map_no_repeats_sorted_optimal'
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) v == true /\
    List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) v == true /\
    List.Tot.no_repeats_p (List.Tot.map fst v)
  ))
  (ensures (valid_raw_data_item_map v == true))
= list_no_setoid_repeats_no_repeats (List.Tot.map fst v);
  list_no_setoid_repeats_map_elim
    fst
    v
    (map_entry_order raw_equiv _)
    ( = )
    (fun x x' ->
      List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v;
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) v;
      raw_equiv_sorted_optimal_eq order (fst x) (fst x')
    )

let valid_raw_data_item_map_no_repeats_sorted_optimal
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) v == true /\
    List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) v == true
  ))
  (ensures (valid_raw_data_item_map v == true <==> List.Tot.no_repeats_p (List.Tot.map fst v)))
= Classical.move_requires valid_raw_data_item_map_no_repeats v;
  Classical.move_requires (valid_raw_data_item_map_no_repeats_sorted_optimal' order) v

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

(* Equivalence and map access *)

let list_setoid_assoc_sorted_optimal
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (x: raw_data_item)
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    raw_data_item_ints_optimal x == true /\
    raw_data_item_sorted order x == true /\
    List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) l == true /\
    List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) l == true
  ))
  (ensures (
    list_setoid_assoc raw_equiv x l == List.Tot.assoc x l
  ))
= list_setoid_assoc_ext
    raw_equiv
    ( = )
    x
    l
    (fun y ->
      List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) l;
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) l;
      raw_equiv_sorted_optimal_eq order x (fst y)
    );
  list_setoid_assoc_eqtype x l

let rec list_setoid_assoc_valid_equiv'
  (x1: raw_data_item)
  (l1l l1r: list (raw_data_item & raw_data_item))
  (x2: raw_data_item)
  (l2: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    let l1 = l1l `List.Tot.append` l1r in
    valid_raw_data_item_map l1 == true /\
    valid_raw_data_item_map l2 == true /\
    list_for_all_exists (holds_on_pair2 raw_equiv) l1 l2 == true /\
    list_for_all_exists (holds_on_pair2 raw_equiv) l2 l1 == true /\
    list_setoid_assoc raw_equiv x1 l1l == None /\
    raw_equiv x1 x2 == true /\
    Some? (list_setoid_assoc raw_equiv x1 l1r)
  ))
  (ensures (
    match list_setoid_assoc raw_equiv x1 l1r, list_setoid_assoc raw_equiv x2 l2 with
    | Some v1, Some v2 -> raw_equiv v1 v2
    | _ -> False
  ))
  (decreases l1r)
= let xv1 :: q = l1r in
  let (x1', v1) = xv1 in
  if raw_equiv x1 x1'
  then begin
    List.Tot.for_all_append (list_existsb2 (holds_on_pair2 raw_equiv) l2) l1l l1r;
    let xv2mem = list_existsb_elim (holds_on_pair2 raw_equiv xv1) l2 in
    raw_equiv_sym x1 x2;
    raw_equiv_trans x2 x1 x1';
    raw_equiv_trans x2 x1' (fst xv2mem);
    list_setoid_assoc_mem_elim raw_equiv l2 xv2mem x2;
    let Some v2 = list_setoid_assoc raw_equiv x2 l2 in
    if raw_equiv v1 v2
    then ()
    else begin
      let Some x2'' = list_setoid_assoc_mem raw_equiv x2 l2 in
      let l1 = l1l `List.Tot.append` l1r in
      List.Tot.for_all_mem (list_existsb2 (holds_on_pair2 raw_equiv) l1) l2;
      let xv2'' = (x2'', v2) in
      let xv1'' = list_existsb_elim (holds_on_pair2 raw_equiv xv2'') l1 in
      let (x1'', v1'') = xv1'' in
      List.Tot.append_memP l1l l1r xv1'';
      raw_equiv_trans x1 x2 x2'';
      raw_equiv_trans x1 x2'' x1'';
      if FStar.StrongExcludedMiddle.strong_excluded_middle (List.Tot.memP xv1'' l1l)
      then begin
        list_setoid_assoc_mem_elim raw_equiv l1l xv1'' x1
      end
      else begin
        raw_equiv_sym v2 v1'';
        assert (List.Tot.memP xv1'' q);
        list_no_setoid_repeats_append_elim_r (map_entry_order raw_equiv _) l1l l1r;
        raw_equiv_sym x1 x1';
        raw_equiv_trans x1' x1 x1'';
        list_existsb_intro (map_entry_order raw_equiv _ xv1) q xv1''
      end
    end
  end
  else begin
    list_setoid_assoc_append raw_equiv x1 l1l [xv1];
    List.Tot.append_assoc l1l [xv1] q;
    list_setoid_assoc_valid_equiv' x1 (l1l `List.Tot.append` [xv1]) q x2 l2
  end

let list_setoid_assoc_valid_equiv
  (x1: raw_data_item)
  (l1: list (raw_data_item & raw_data_item))
  (x2: raw_data_item)
  (l2: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    valid_raw_data_item_map l1 == true /\
    valid_raw_data_item_map l2 == true /\
    list_for_all_exists (holds_on_pair2 raw_equiv) l1 l2 == true /\
    list_for_all_exists (holds_on_pair2 raw_equiv) l2 l1 == true /\
    raw_equiv x1 x2 == true
  ))
  (ensures (
    match list_setoid_assoc raw_equiv x1 l1, list_setoid_assoc raw_equiv x2 l2 with
    | None, None -> True
    | Some v1, Some v2 -> raw_equiv v1 v2
    | _ -> False
  ))
= if Some? (list_setoid_assoc raw_equiv x1 l1)
  then list_setoid_assoc_valid_equiv' x1 [] l1 x2 l2
  else if Some? (list_setoid_assoc raw_equiv x2 l2)
  then begin
    raw_equiv_sym x1 x2;
    list_setoid_assoc_valid_equiv' x2 [] l2 x1 l1
  end
  else ()

(* When there are no maps in map keys, equivalence and absence of
   setoid duplicates can be checked in constant stack space. *)

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
