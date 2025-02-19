module CBOR.Spec.API.Format
module RV = CBOR.Spec.Raw.Valid
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
    if RV.raw_data_item_ints_optimal y && RS.raw_data_item_sorted RS.deterministically_encoded_cbor_map_key_order y
    then begin
      RV.raw_data_item_sorted_optimal_valid RS.deterministically_encoded_cbor_map_key_order y;
      R.mk_det_raw_cbor_mk_cbor y;
      Some (R.mk_cbor y, n)
    end
    else None

let cbor_det_parse_prefix x =
  RF.parse_cbor_prefix x

let cbor_det_serialize_parse x =
  RF.serialize_parse_cbor (R.mk_det_raw_cbor x)

let cbor_det_serialize_tag tag =
  RF.serialize_cbor_tag (RF.mk_raw_uint64 tag)

let cbor_det_serialize_tag_length tag =
  RF.serialize_cbor_tag_length (RF.mk_raw_uint64 tag)

let cbor_det_serialize_tag_correct tag payload =
  R.mk_cbor_eq (R.Tagged (RF.mk_raw_uint64 tag) (R.mk_det_raw_cbor payload));
  R.mk_det_raw_cbor_mk_cbor (R.Tagged (RF.mk_raw_uint64 tag) (R.mk_det_raw_cbor payload));
  assert (R.mk_det_raw_cbor (pack (CTagged tag payload)) == R.Tagged (RF.mk_raw_uint64 tag) (R.mk_det_raw_cbor payload));
  RF.serialize_cbor_tag_correct (RF.mk_raw_uint64 tag) (R.mk_det_raw_cbor payload)

let rec list_map_mk_det_raw_cbor_correct
  (l: list cbor)
: Lemma
  (ensures (
    let l' = List.Tot.map R.mk_det_raw_cbor l in
    List.Tot.for_all R.raw_data_item_ints_optimal l' /\
    List.Tot.for_all (R.raw_data_item_sorted R.deterministically_encoded_cbor_map_key_order) l'
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
  R.serialize_cbor_list (List.Tot.map R.mk_det_raw_cbor l)

let cbor_det_serialize_list_nil () =
  R.serialize_cbor_list_nil ()

let cbor_det_serialize_list_cons a q =
  R.serialize_cbor_list_cons (R.mk_det_raw_cbor a) (List.Tot.map R.mk_det_raw_cbor q)
