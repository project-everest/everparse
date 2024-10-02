module CBOR.Spec.Raw
include CBOR.Spec.Type

module R = CBOR.Spec.Raw.Valid
module U = CBOR.Spec.Util

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
  | R.Map _ v1, CMap v2 -> mk_cbor_match_map v1 v2
  | R.Array _ v1, CArray v2 -> List.Tot.map mk_cbor v1 == v2
  | _ -> False
  ))
