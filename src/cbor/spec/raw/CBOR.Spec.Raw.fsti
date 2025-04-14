module CBOR.Spec.Raw
include CBOR.Spec.Raw.Sort
include CBOR.Spec.API.Type

module RF = CBOR.Spec.Raw.Format
module R = CBOR.Spec.Raw.Sort
module RS = CBOR.Spec.Raw.Sort
module U = CBOR.Spec.Util
module U64 = FStar.UInt64

val mk_cbor (r: R.raw_data_item) : Tot cbor

val mk_cbor_equiv (r1 r2: R.raw_data_item) : Lemma
  (requires (
    R.valid_raw_data_item r1 == true /\
    R.valid_raw_data_item r2 == true
  ))
  (ensures (
    R.raw_equiv r1 r2 <==> mk_cbor r1 == mk_cbor r2
  ))

let mk_cbor_match_map_elem
  (r: list (R.raw_data_item & R.raw_data_item))
  (m: cbor_map)
  (x: R.raw_data_item)
: Tot prop
= R.valid_raw_data_item x ==>
  begin match U.list_setoid_assoc R.raw_equiv x r, cbor_map_get m (mk_cbor x) with
  | None, None -> True
  | Some v1, Some v2 -> R.valid_raw_data_item v1 /\ mk_cbor v1 == v2
  | _ -> False
  end

let mk_cbor_match_map
  (r: list (R.raw_data_item & R.raw_data_item))
  (m: cbor_map)
: Tot prop
= forall (x: R.raw_data_item) . mk_cbor_match_map_elem r m x

val mk_cbor_eq
  (r: R.raw_data_item)
: Lemma
  (requires (R.valid_raw_data_item r == true))
  (ensures (match r, unpack (mk_cbor r) with
  | R.Simple v1, CSimple v2 -> v1 == v2
  | R.Int64 ty1 v1, CInt64 ty2 v2 -> ty1 == ty2 /\ v1.value == v2
  | R.String ty1 _ v1, CString ty2 v2 -> ty1 == ty2 /\ v1 == v2
  | R.Tagged tag1 v1, CTagged tag2 v2 -> tag1.value == tag2 /\ mk_cbor v1 == v2
  | R.Map _ v1, CMap v2 ->
    cbor_map_length v2 == List.Tot.length v1 /\
    mk_cbor_match_map v1 v2
  | R.Array _ v1, CArray v2 -> List.Tot.map mk_cbor v1 == v2
  | _ -> False
  ))

val mk_det_raw_cbor (c: cbor) : Pure R.raw_data_item
  (requires True)
  (ensures fun y ->
    R.raw_data_item_ints_optimal y /\
    RS.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order y /\
    R.valid_raw_data_item y /\
    mk_cbor y == c
  )

let mk_det_raw_cbor_inj (c1 c2: cbor) : Lemma
  (requires (mk_det_raw_cbor c1 == mk_det_raw_cbor c2))
  (ensures (c1 == c2))
= ()

let mk_det_raw_cbor_inj_strong (c1 c2: cbor) : Lemma
  (requires (R.raw_equiv (mk_det_raw_cbor c1) (mk_det_raw_cbor c2)))
  (ensures (c1 == c2))
= mk_cbor_equiv (mk_det_raw_cbor c1) (mk_det_raw_cbor c2)

let mk_det_raw_cbor_mk_cbor (x: R.raw_data_item) : Lemma
  (requires (
    R.raw_data_item_ints_optimal x /\
    RS.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order x
  ))
  (ensures (
    R.valid_raw_data_item x /\
    mk_det_raw_cbor (mk_cbor x) == x
  ))
= R.raw_data_item_sorted_optimal_valid RF.deterministically_encoded_cbor_map_key_order x;
  mk_cbor_equiv (mk_det_raw_cbor (mk_cbor x)) x;
  R.raw_equiv_sorted_optimal RF.deterministically_encoded_cbor_map_key_order (mk_det_raw_cbor (mk_cbor x)) x

let mk_det_raw_cbor_map_entry
  (x: (cbor & cbor))
: Tot (R.raw_data_item & R.raw_data_item)
= (mk_det_raw_cbor (fst x), mk_det_raw_cbor (snd x))

val no_repeats_map_fst_mk_det_raw_cbor_map_entry
  (l: list (cbor & cbor))
: Lemma
  (List.Tot.no_repeats_p (List.Tot.map fst l) <==> List.Tot.no_repeats_p (List.Tot.map fst (List.Tot.map mk_det_raw_cbor_map_entry l)))

val mk_det_raw_cbor_map
  (l: list (cbor & cbor))
  (len: FStar.UInt64.t)
: Pure cbor
  (requires (List.Tot.no_repeats_p (List.Tot.map fst l) /\
    FStar.UInt64.v len == List.Tot.length l
  ))
  (ensures (fun res ->
    match unpack res with
    | CMap m ->
      let l1 = List.Tot.map mk_det_raw_cbor_map_entry l in
      let l' = RS.cbor_map_sort RF.deterministically_encoded_cbor_map_key_order l1 in
      List.Tot.no_repeats_p (List.Tot.map fst l1) /\
      List.Tot.length l == FStar.UInt64.v len /\
      List.Tot.length l' == FStar.UInt64.v len /\
      cbor_map_length m == FStar.UInt64.v len /\
      (forall x . List.Tot.assoc x l == cbor_map_get m x) /\
      mk_det_raw_cbor res == R.Map (R.mk_raw_uint64 len) l'
    | _ -> False
  ))

val mk_det_raw_cbor_map_raw
  (m: cbor_map)
: Pure (list (raw_data_item & raw_data_item))
    (requires True)
    (ensures (fun res ->
      List.Tot.sorted (map_entry_order RF.deterministically_encoded_cbor_map_key_order _) res /\
      List.Tot.length res == cbor_map_length m /\
      List.Tot.for_all (U.holds_on_pair (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order)) res /\
      List.Tot.for_all (U.holds_on_pair R.raw_data_item_ints_optimal) res
    ))

val mk_det_raw_cbor_map_raw_singleton
  (key: cbor)
  (value: cbor)
: Lemma
  (mk_det_raw_cbor_map_raw (cbor_map_singleton key value) == [mk_det_raw_cbor key, mk_det_raw_cbor value])

val mk_det_raw_cbor_map_raw_assoc
  (m: cbor_map)
  (k: cbor)
: Lemma
  (mk_cbor_match_map_elem (mk_det_raw_cbor_map_raw m) m (mk_det_raw_cbor k))

val mk_det_raw_cbor_map_raw_mem
  (m: cbor_map)
  (x: (raw_data_item & raw_data_item))
: Lemma
  (let l = mk_det_raw_cbor_map_raw m in
  List.Tot.memP x l <==> (
    U.holds_on_pair (R.raw_data_item_sorted RF.deterministically_encoded_cbor_map_key_order) x /\
    U.holds_on_pair R.raw_data_item_ints_optimal x /\
    cbor_map_get m (mk_cbor (fst x)) == Some (mk_cbor (snd x))
  ))

val mk_cbor_eq_map
  (x: cbor)
: Lemma
  (requires (CMap? (unpack x)))
  (ensures (match mk_det_raw_cbor x, unpack x with
  | Map len l, CMap m ->
    len == mk_raw_uint64 (U64.uint_to_t (cbor_map_length m)) /\
    l == mk_det_raw_cbor_map_raw m
  | _ -> False
  ))

unfold
let mk_det_raw_cbor_map_raw_snoc_post
  (m: cbor_map)
  (key: cbor)
  (value: cbor)
: Tot prop
=
    let l = mk_det_raw_cbor_map_raw m in
    let ol' = CBOR.Spec.Raw.Map.map_insert RF.cbor_compare l (mk_det_raw_cbor key, mk_det_raw_cbor value) in
    (None? ol' <==> cbor_map_defined key m) /\
    (Some? ol' ==> ol' == Some (mk_det_raw_cbor_map_raw (cbor_map_union m (cbor_map_singleton key value))))

val mk_det_raw_cbor_map_raw_snoc
  (m: cbor_map)
  (key: cbor)
  (value: cbor)
: Lemma
  (
    mk_det_raw_cbor_map_raw_snoc_post m key value
  )
