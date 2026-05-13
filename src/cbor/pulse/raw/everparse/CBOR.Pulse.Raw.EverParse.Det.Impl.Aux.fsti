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

val det_raw_list_eq (l: list Spec.cbor)
: Lemma (det_raw_list l == List.Tot.map SpecRaw.mk_det_raw_cbor l)
        [SMTPat (det_raw_list l)]

val length_det_raw_list (l: list Spec.cbor)
  : Lemma (List.Tot.length (det_raw_list l) == List.Tot.length l)
          [SMTPat (List.Tot.length (det_raw_list l))]

val det_raw_list_inverse (l: list SpecRawBase.raw_data_item)
: Lemma
    (requires
      List.Tot.for_all Optimal.raw_data_item_ints_optimal l /\
      List.Tot.for_all (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order) l)
    (ensures det_raw_list (List.Tot.map SpecRaw.mk_cbor l) == l)

val det_raw_list_take_eq (l: list Spec.cbor) (n: nat)
: Lemma
    (det_raw_list (fst (List.Tot.splitAt n l)) ==
     LowParse.PulseParse.Iterator.list_narrow (det_raw_list l) 0 n)

val mk_det_raw_cbor_array_eq (y: Spec.cbor) (l: list Spec.cbor)
: Lemma
    (requires
      FStar.UInt.fits (List.Tot.length l) 64 /\
      Spec.unpack y == Spec.CArray l)
    (ensures
       SpecRawBase.Array? (SpecRaw.mk_det_raw_cbor y) /\
       (SpecRawBase.Array?.v (SpecRaw.mk_det_raw_cbor y) <: list SpecRawBase.raw_data_item) == det_raw_list l)

(* ====================================================================
   Map-entry analogues of det_raw_list. Used as the underlying
   spec list for the (still-pending) cbor_det_map_iterator_match. *)

val det_raw_map_entries
  (l: list (Spec.cbor & Spec.cbor))
: Tot (list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))

val mk_det_raw_cbor_inj_map_entries (l1 l2: list (Spec.cbor & Spec.cbor))
: Lemma
    (requires det_raw_map_entries l1 == det_raw_map_entries l2)
    (ensures l1 == l2)

val det_raw_map_entries_eq
  (l: list (Spec.cbor & Spec.cbor))
: Lemma
    (det_raw_map_entries l == List.Tot.map SpecRaw.mk_det_raw_cbor_map_entry l)
    [SMTPat (det_raw_map_entries l)]

val length_det_raw_map_entries
  (l: list (Spec.cbor & Spec.cbor))
: Lemma
    (List.Tot.length (det_raw_map_entries l) == List.Tot.length l)
    [SMTPat (List.Tot.length (det_raw_map_entries l))]

(* For map iterator next: convert raw map entry (pair of raw_data_item) back
   to the spec pair (cbor & cbor). *)

val list_map_mk_cbor_mk_det_raw_cbor_map_entry (l: list (Spec.cbor & Spec.cbor))
: Lemma (ensures (
    List.Tot.map SpecRaw.mk_cbor_map_entry (det_raw_map_entries l) == l
  ))

val list_map_mk_det_raw_cbor_correct_map_entries (l: list (Spec.cbor & Spec.cbor))
: Lemma (ensures (
    let l' = det_raw_map_entries l in
    List.Tot.for_all
      (CBOR.Spec.Util.holds_on_pair Optimal.raw_data_item_ints_optimal) l' /\
    List.Tot.for_all
      (CBOR.Spec.Util.holds_on_pair (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order)) l'
  ))

val det_raw_map_entries_inverse (l: list (SpecRawBase.raw_data_item & SpecRawBase.raw_data_item))
: Lemma
    (requires
      List.Tot.for_all
        (CBOR.Spec.Util.holds_on_pair Optimal.raw_data_item_ints_optimal) l /\
      List.Tot.for_all
        (CBOR.Spec.Util.holds_on_pair (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order)) l)
    (ensures det_raw_map_entries (List.Tot.map SpecRaw.mk_cbor_map_entry l) == l)

val mk_det_raw_cbor_map_entry_mk_cbor_map_entry (x: SpecRawBase.raw_data_item & SpecRawBase.raw_data_item)
: Lemma
    (requires
      CBOR.Spec.Util.holds_on_pair Optimal.raw_data_item_ints_optimal x /\
      CBOR.Spec.Util.holds_on_pair (Optimal.raw_data_item_sorted Format.deterministically_encoded_cbor_map_key_order) x)
    (ensures (SpecRaw.mk_det_raw_cbor_map_entry (SpecRaw.mk_cbor_map_entry x) == x))
