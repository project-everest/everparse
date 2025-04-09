module CBOR.Spec.Raw.Optimal
include CBOR.Spec.Raw.Valid
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

unfold
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

let raw_data_item_uint64_optimize_map_length (x: raw_data_item) : Lemma
  (match x, raw_data_item_uint64_optimize x with
  | Map len _, Map len' _ -> len.value == len'.value
  | Map _ _, _ | _, Map _ _ -> False
  | _ -> True
  )
= raw_data_item_fmap_eq raw_data_item_uint64_optimize_elem x

let rec raw_data_item_uint64_optimize_size (x: raw_data_item) : Lemma
  (ensures (raw_data_item_size (raw_data_item_uint64_optimize x) == raw_data_item_size x))
  (decreases x)
= raw_data_item_size_eq x;
  raw_data_item_size_eq (raw_data_item_uint64_optimize x);
  raw_data_item_fmap_eq raw_data_item_uint64_optimize_elem x;
//  assert_norm (raw_data_item_uint64_optimize == raw_data_item_fmap raw_data_item_uint64_optimize_elem);
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

let raw_data_item_uint64_optimize_equiv = raw_data_item_uint64_optimize_valid

(* Sorting map keys *)

noextract
let raw_data_item_sorted_elem (order: (raw_data_item -> raw_data_item -> bool)) (x: raw_data_item) : Tot bool
= match x with
  | Map _ l ->
      FStar.List.Tot.sorted (map_entry_order order _) l
  | _ -> true

noextract
unfold
let raw_data_item_sorted (order: (raw_data_item -> raw_data_item -> bool)) : Tot (raw_data_item -> bool)
= holds_on_raw_data_item (raw_data_item_sorted_elem order)

let list_sorted_map_assoc_ext
  (#t: eqtype)
  (#t': Type)
  (order: t -> t -> bool {
    order_irrefl order /\
    order_trans order
  })
  (l1 l2: list (t & t'))
  (sq1: squash (List.Tot.sorted (map_entry_order order _) l1 == true))
  (sq2: squash (List.Tot.sorted (map_entry_order order _) l2 == true))
  (prf: (x: t) -> Lemma
    (List.Tot.assoc x l1 == List.Tot.assoc x l2)
  )
: Lemma
  (ensures (
    l1 == l2
  ))
= Classical.forall_intro prf;
  CBOR.Spec.Raw.Map.list_sorted_map_assoc_ext order l1 l2

let rec raw_equiv_sorted_optimal
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (x1 x2: raw_data_item)
: Lemma
  (requires (
    raw_equiv2 x1 x2 /\
    raw_data_item_sorted order x1 /\
    raw_data_item_sorted order x2 /\
    raw_data_item_ints_optimal x1 /\
    raw_data_item_ints_optimal x2
  ))
  (ensures (x1 == x2))
  (decreases (raw_data_item_size x1 + raw_data_item_size x2))
= equiv_eq basic_data_model x1 x2;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x1;
  holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) x2;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x1;
  holds_on_raw_data_item_eq raw_data_item_ints_optimal_elem x2;
  raw_data_item_size_eq x1;
  raw_data_item_size_eq x2;
  if x1 = x2 then () else
  match x1, x2 with
  | Simple _, Simple _ -> ()
  | Int64 _ v1, Int64 _ v2 ->
    raw_uint64_optimal_unique v1 v2
  | String _ v1 _, String _ v2 _ ->
    raw_uint64_optimal_unique v1 v2
  | Tagged tag1 v1, Tagged tag2 v2 ->
    raw_uint64_optimal_unique tag1 tag2;
    raw_equiv_sorted_optimal order v1 v2;
    ()
  | Array len1 l1, Array len2 l2 ->
    list_for_all2_length (equiv basic_data_model) l1 l2;
    raw_uint64_optimal_unique len1 len2;
//    assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
    list_for_all2_prod (raw_data_item_sorted order) (raw_data_item_sorted order) l1 l2;
    list_for_all2_prod raw_data_item_ints_optimal raw_data_item_ints_optimal l1 l2;
    list_for_all2_andp_intro
      (prodp (raw_data_item_sorted order) (raw_data_item_sorted order))
      (prodp raw_data_item_ints_optimal raw_data_item_ints_optimal)
      l1 l2;
    list_for_all2_andp_intro
      (andp2
        (prodp (raw_data_item_sorted order) (raw_data_item_sorted order))
        (prodp raw_data_item_ints_optimal raw_data_item_ints_optimal))
      raw_equiv2
      l1 l2;
    list_for_all2_implies
      (andp2
        (andp2
          (prodp (raw_data_item_sorted order) (raw_data_item_sorted order))
          (prodp raw_data_item_ints_optimal raw_data_item_ints_optimal))
        raw_equiv2
      )
      ( = )
      l1 l2
      (fun x1' x2' ->
        list_sum_memP raw_data_item_size l1 x1';
        list_sum_memP raw_data_item_size l2 x2';
        raw_equiv_sorted_optimal order x1' x2'
      );
    list_for_all2_equals l1 l2
  | Map len1 l1, Map len2 l2 ->
    let list_assoc_eq_setoid_assoc
      (l1' l2' : list (raw_data_item & raw_data_item))
      (k: raw_data_item)
    : Lemma
      (requires (
        List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) l1' /\
        List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) l2' /\
        List.Tot.for_all (holds_on_pair (raw_data_item_ints_optimal)) l1' /\
        List.Tot.for_all (holds_on_pair (raw_data_item_ints_optimal)) l2' /\
        list_sum (pair_sum raw_data_item_size raw_data_item_size) l1' + list_sum (pair_sum raw_data_item_size raw_data_item_size) l2' < raw_data_item_size x1 + raw_data_item_size x2 /\
        Some? (List.Tot.assoc k l1') /\
        List.Tot.for_all (setoid_assoc_eq (raw_equiv2) (raw_equiv2) l2') l1'
      ))
      (ensures (
        List.Tot.assoc k l1' == List.Tot.assoc k l2'
      ))
    = let Some v = List.Tot.assoc k l1' in
      list_assoc_mem_intro k v l1';
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) l1' (k, v);
      List.Tot.for_all_mem (setoid_assoc_eq raw_equiv2 raw_equiv2 l2') l1';
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) l1';
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_ints_optimal)) l1';
      list_setoid_assoc_eqtype k l2';
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) l2';
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_ints_optimal)) l2';
      list_setoid_assoc_equiv_gen raw_equiv2 ( = ) l2' k k (fun kv' ->
        list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) l2' kv';
        let k' = fst kv' in
        equiv_refl_forall basic_data_model;
        if raw_equiv2 k k'
        then raw_equiv_sorted_optimal order k (fst kv')
        else ()
      );
      let Some v' = List.Tot.assoc k l2' in
      list_assoc_mem_intro k v' l2';
      list_sum_memP (pair_sum raw_data_item_size raw_data_item_size) l2' (k, v');
      raw_equiv_sorted_optimal order v v';
      assert (List.Tot.assoc k l1' == List.Tot.assoc k l2')
    in
    let prf_assoc (k: raw_data_item) : Lemma
      (List.Tot.assoc k l1 == List.Tot.assoc k l2)
    = match List.Tot.assoc k l1 with
      | Some _ -> list_assoc_eq_setoid_assoc l1 l2 k
      | None ->
        match List.Tot.assoc k l2 with
        | Some _ -> list_assoc_eq_setoid_assoc l2 l1 k
        | None -> ()
    in
    list_sorted_map_assoc_ext order l1 l2 () () prf_assoc;
    raw_uint64_optimal_unique len1 len2

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
  (ensures (raw_equiv2 x1 x2 == (x1 = x2)))
= if raw_equiv2 x1 x2
  then raw_equiv_sorted_optimal order x1 x2
  else if x1 = x2
  then equiv_refl basic_data_model x1
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
  (ensures (valid_map basic_data_model v == true))
= let v' = (List.Tot.map fst v) in
  list_no_setoid_repeats_no_repeats v';
  assert (list_no_setoid_repeats ( = ) v');
  list_no_setoid_repeats_implies
    ( = )
    (raw_equiv2)
    v'
    (fun x x' ->
      let y = list_memP_map_elim fst x v in
      let y' = list_memP_map_elim fst x' v in
      List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) v;
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) v;
      raw_equiv_sorted_optimal_eq order x x'
    )

let valid_raw_data_item_map_no_repeats
  (v: list (raw_data_item & raw_data_item))
: Lemma
  (requires (valid_map basic_data_model v == true))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst v)))
= list_no_setoid_repeats_implies
    raw_equiv2
    ( = )
    (List.Tot.map fst v)
    (fun x x' -> equiv_refl basic_data_model x);
  list_no_setoid_repeats_no_repeats (List.Tot.map fst v)

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
  (ensures (valid_map basic_data_model v == true <==> List.Tot.no_repeats_p (List.Tot.map fst v)))
= Classical.move_requires valid_raw_data_item_map_no_repeats v;
  Classical.move_requires (valid_raw_data_item_map_no_repeats_sorted_optimal' order) v

let rec raw_data_item_sorted_optimal_valid_aux
  (order: (raw_data_item -> raw_data_item -> bool) {
    order_irrefl order /\
    order_trans order
  })
  (l: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) l /\
    List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) l /\
    FStar.List.Tot.sorted (map_entry_order order _) l
  ))
  (ensures (
    list_no_setoid_repeats (map_entry_order raw_equiv2 _) l
  ))
  (decreases l)
= match l with
  | [] -> ()
  | a :: q ->
    raw_data_item_sorted_optimal_valid_aux order q;
    if List.Tot.existsb (map_entry_order raw_equiv2 _ a) q
    then begin
      let a' = list_existsb_elim (map_entry_order raw_equiv2 _ a) q in
      list_sorted_memP (map_entry_order order _) a q a';
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) q;
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_ints_optimal)) q;
      raw_equiv_sorted_optimal order (fst a) (fst a')
    end
    else ()

let raw_data_item_sorted_optimal_valid
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
  (ensures (valid basic_data_model x1))
= valid_eq' basic_data_model x1;
  holds_on_raw_data_item_andp (raw_data_item_sorted_elem order) raw_data_item_ints_optimal_elem x1;
  holds_on_raw_data_item_implies
    (andp (raw_data_item_sorted_elem order) raw_data_item_ints_optimal_elem)
    (valid_item basic_data_model)
    (fun x ->
      match x with
      | Map len v ->
        holds_on_raw_data_item_andp (raw_data_item_sorted_elem order) raw_data_item_ints_optimal_elem x;
          holds_on_raw_data_item_eq (raw_data_item_sorted_elem order) (Map len v);
          holds_on_raw_data_item_eq (raw_data_item_ints_optimal_elem) (Map len v);
          assert (List.Tot.for_all (holds_on_pair (holds_on_raw_data_item raw_data_item_ints_optimal_elem)) v);
          assert_norm (raw_data_item_ints_optimal == holds_on_raw_data_item raw_data_item_ints_optimal_elem);
          assert (List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) v);
          raw_data_item_sorted_optimal_valid_aux order v;
          valid_map_eq basic_data_model v;
          assert (valid_map basic_data_model v == true)
      | _ -> ()
    )
    x1

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
    list_setoid_assoc raw_equiv2 x l == List.Tot.assoc x l
  ))
= list_setoid_assoc_ext
    raw_equiv2
    ( = )
    x
    l
    (fun y ->
      List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) l;
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) l;
      raw_equiv_sorted_optimal_eq order x (fst y)
    );
  list_setoid_assoc_eqtype x l

let list_assoc_sorted_optimal_setoid_assoc_eq
  (order: raw_data_item -> raw_data_item -> bool {
    order_irrefl order /\
    order_trans order
  })
  (l1: list (raw_data_item & raw_data_item))
  (l2: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) l1 == true /\
    List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) l1 == true /\
    List.Tot.for_all (holds_on_pair raw_data_item_ints_optimal) l2 == true /\
    List.Tot.for_all (holds_on_pair (raw_data_item_sorted order)) l2 == true /\
    List.Tot.no_repeats_p (List.Tot.map fst l1) /\
    List.Tot.no_repeats_p (List.Tot.map fst l2) /\
    (forall x . List.Tot.assoc x l1 == List.Tot.assoc x l2)
  ))
  (ensures (
    List.Tot.for_all (setoid_assoc_eq (raw_equiv2) (raw_equiv2) l1) l2
  ))
= list_for_all_intro
    (setoid_assoc_eq (raw_equiv2) (raw_equiv2) l1)
    l2
    (fun x ->
      List.Tot.for_all_mem (holds_on_pair raw_data_item_ints_optimal) l2;
      List.Tot.for_all_mem (holds_on_pair (raw_data_item_sorted order)) l2;
      list_setoid_assoc_sorted_optimal order (fst x) l1;
      list_assoc_no_repeats_mem_elim (fst x) (snd x) l2;
      equiv_refl basic_data_model (snd x)
    )

let list_setoid_assoc_valid_equiv
  (x1: raw_data_item)
  (l1: list (raw_data_item & raw_data_item))
  (x2: raw_data_item)
  (l2: list (raw_data_item & raw_data_item))
: Lemma
  (requires (
    valid_map basic_data_model l1 == true /\
    valid_map basic_data_model l2 == true /\
    List.Tot.for_all (setoid_assoc_eq (raw_equiv2) (raw_equiv2) l1) l2 /\
    List.Tot.for_all (setoid_assoc_eq (raw_equiv2) (raw_equiv2) l2) l1 /\
    raw_equiv2 x1 x2 == true
  ))
  (ensures (
    match list_setoid_assoc raw_equiv2 x1 l1, list_setoid_assoc raw_equiv2 x2 l2 with
    | None, None -> True
    | Some v1, Some v2 -> raw_equiv2 v1 v2
    | _ -> False
  ))
= equiv_refl_forall basic_data_model;
  equiv_sym_forall basic_data_model;
  equiv_trans_forall basic_data_model;
  match list_setoid_assoc raw_equiv2 x1 l1 with
  | Some v1 ->
    let Some k1 = list_setoid_assoc_mem raw_equiv2 x1 l1 in
    List.Tot.for_all_mem (setoid_assoc_eq (raw_equiv2) (raw_equiv2) l2) l1;
    list_setoid_assoc_equiv raw_equiv2 l2 x1 k1;
    list_setoid_assoc_equiv raw_equiv2 l2 x1 x2;
    ()
  | _ ->
    begin match list_setoid_assoc raw_equiv2 x2 l2 with
    | None -> ()
    | Some v2 ->
      let Some k2 = list_setoid_assoc_mem raw_equiv2 x2 l2 in
      List.Tot.for_all_mem (setoid_assoc_eq (raw_equiv2) (raw_equiv2) l1) l2;
      list_setoid_assoc_equiv raw_equiv2 l1 x2 k2;
      list_setoid_assoc_equiv raw_equiv2 l1 x1 x2;      
      ()
    end
