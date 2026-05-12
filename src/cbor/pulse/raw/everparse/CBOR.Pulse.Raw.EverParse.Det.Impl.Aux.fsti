module CBOR.Pulse.Raw.EverParse.Det.Impl.Aux

module Spec = CBOR.Spec.API.Format
module SpecRawBase = CBOR.Spec.Raw.Base
module SpecRaw = CBOR.Spec.Raw

val mk_det_raw_cbor_tot (c: Spec.cbor) : Tot SpecRawBase.raw_data_item

val det_raw_list (l: list Spec.cbor) : Tot (list SpecRawBase.raw_data_item)

module Optimal = CBOR.Spec.Raw.Optimal
module Format = CBOR.Spec.Raw.Format

val list_map_mk_det_raw_cbor_correct (l: list Spec.cbor)
: Lemma (ensures (
    let l' = det_raw_list l in
    List.Tot.for_all Optimal.raw_data_item_ints_optimal l' /\
    List.Tot.for_all (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order) l'
  ))

val list_map_mk_cbor_mk_det_raw_cbor (l: list Spec.cbor)
: Lemma (ensures (List.Tot.map SpecRaw.mk_cbor (det_raw_list l) == l))

val mk_det_raw_cbor_inj_map (l1 l2: list Spec.cbor)
: Lemma
    (requires det_raw_list l1 == det_raw_list l2)
    (ensures l1 == l2)

val length_det_raw_list (l: list Spec.cbor)
  : Lemma (List.Tot.length (det_raw_list l) == List.Tot.length l)
          [SMTPat (List.Tot.length (det_raw_list l))]

val det_raw_list_inverse (l: list SpecRawBase.raw_data_item)
: Lemma
    (requires
      List.Tot.for_all Optimal.raw_data_item_ints_optimal l /\
      List.Tot.for_all (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order) l)
    (ensures det_raw_list (List.Tot.map SpecRaw.mk_cbor l) == l)

val mk_det_raw_cbor_array_eq (y: Spec.cbor) (l: list Spec.cbor)
: Lemma
    (requires
      FStar.UInt.fits (List.Tot.length l) 64 /\
      Spec.unpack y == Spec.CArray l)
    (ensures
       SpecRawBase.Array? (SpecRaw.mk_det_raw_cbor y) /\
       (SpecRawBase.Array?.v (SpecRaw.mk_det_raw_cbor y) <: list SpecRawBase.raw_data_item) == det_raw_list l)
