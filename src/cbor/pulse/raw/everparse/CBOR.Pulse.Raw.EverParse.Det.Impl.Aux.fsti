module CBOR.Pulse.Raw.EverParse.Det.Impl.Aux

module Spec = CBOR.Spec.API.Format
module SpecRawBase = CBOR.Spec.Raw.Base
module SpecRaw = CBOR.Spec.Raw

val mk_det_raw_cbor_tot (c: Spec.cbor) : Tot SpecRawBase.raw_data_item

val det_raw_list (l: list Spec.cbor) : Tot (list SpecRawBase.raw_data_item)

val mk_det_raw_cbor_inj_map (l1 l2: list Spec.cbor)
: Lemma
    (requires det_raw_list l1 == det_raw_list l2)
    (ensures l1 == l2)

val length_det_raw_list (l: list Spec.cbor)
  : Lemma (List.Tot.length (det_raw_list l) == List.Tot.length l)
          [SMTPat (List.Tot.length (det_raw_list l))]

val mk_det_raw_cbor_array_eq (y: Spec.cbor) (l: list Spec.cbor)
: Lemma
    (requires
      FStar.UInt.fits (List.Tot.length l) 64 /\
      Spec.unpack y == Spec.CArray l)
    (ensures
       SpecRawBase.Array? (SpecRaw.mk_det_raw_cbor y) /\
       (SpecRawBase.Array?.v (SpecRaw.mk_det_raw_cbor y) <: list SpecRawBase.raw_data_item) == det_raw_list l)
