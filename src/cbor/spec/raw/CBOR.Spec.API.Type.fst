module CBOR.Spec.API.Type

module RF = CBOR.Spec.Raw.Format
module R = CBOR.Spec.Raw.Sort
module DM = CBOR.Spec.Raw.DataModel

unfold let order = RF.deterministically_encoded_cbor_map_key_order

unfold let compare : (compare: (R.raw_data_item -> R.raw_data_item -> int) { R.compare_prop order compare })
=
  RF.cbor_compare

let cbor = DM.cbor order compare

let cbor_map = DM.cbor_map order compare

let cbor_map_get = DM.cbor_map_get

let cbor_map_get_precedes = DM.cbor_map_get_precedes

let cbor_map_equal_eq (m1 m2: cbor_map) : Lemma
  (ensures DM.cbor_map_equal m1 m2 <==> cbor_map_equal m1 m2)
//  [SMTPat (cbor_map_equal m1 m2)]
= assert_norm (DM.cbor_map_equal m1 m2 <==> cbor_map_equal m1 m2) // FIXME: WHY WHY WHY?

let cbor_map_ext m1 m2 =
  cbor_map_equal_eq m1 m2;
  DM.cbor_map_ext m1 m2

let cbor_map_set_keys = DM.cbor_map_set_keys

let cbor_map_set_keys_mem = DM.cbor_map_set_keys_mem

let cbor_map_length = DM.cbor_map_length

let cbor_map_empty = DM.cbor_map_empty

let cbor_map_get_empty = DM.cbor_map_get_empty

let cbor_map_singleton = DM.cbor_map_singleton

let cbor_map_get_singleton = DM.cbor_map_get_singleton

let cbor_map_filter = DM.cbor_map_filter

let cbor_map_get_filter = DM.cbor_map_get_filter

let cbor_map_length_filter = DM.cbor_map_length_filter

let cbor_map_union = DM.cbor_map_union

let cbor_map_get_union = DM.cbor_map_get_union

let cbor_map_key_list = DM.cbor_map_key_list

let cbor_map_key_list_mem = DM.cbor_map_key_list_mem

let cbor_map_key_list_no_repeats_p = DM.cbor_map_key_list_no_repeats_p

let cbor_map_key_list_length = DM.cbor_map_key_list_length

let cbor_map_fold f x m = DM.cbor_map_fold f x m

let cbor_map_fold_ext = DM.cbor_map_fold_ext

let cbor_map_fold_eq = DM.cbor_map_fold_eq

let cbor_map_fold_eq_idem = DM.cbor_map_fold_eq_idem

let unpack_aux
  (x' : DM.cbor_case order compare)
: cbor_case
=
  match x' with
  | DM.CSimple v -> CSimple v
  | DM.CInt64 ty v -> CInt64 ty v
  | DM.CString ty v -> CString ty v
  | DM.CArray v -> CArray v
  | DM.CMap c -> CMap c
  | DM.CTagged tag v -> CTagged tag v

let unpack m =
  unpack_aux (DM.unpack m)

let pack_aux (x: cbor_case)
: Tot (DM.cbor_case order compare)
=
  match x with
  | CSimple v -> DM.CSimple v
  | CInt64 ty v -> DM.CInt64 ty v
  | CString ty v -> DM.CString ty v
  | CArray v -> DM.CArray v
  | CMap c -> DM.CMap c
  | CTagged tag v -> DM.CTagged tag v
  
let pack x = DM.pack (pack_aux x)

let unpack_pack c = DM.unpack_pack (pack_aux c)

let pack_unpack c = DM.pack_unpack c

let unpack_precedes c = DM.unpack_precedes c
