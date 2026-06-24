module CBOR.Pulse.Raw.EverParse.Nondet.Compare.ListForAll
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.Setoid
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open LowParse.PulseParse.Iterator
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type

inline_for_extraction
val compare_cbor_raw_list_for_all_fuel
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (#equiv: Ghost.erased (raw_data_item -> raw_data_item -> option bool))
  (compare_impl: compare_cbor_raw_fn_fuel_t n equiv)
  (f64: squash SZ.fits_u64)
  (inner_ml: IT.mixed_list (cbor_map_entry cbor_raw))
  (#pm_inner: perm)
  (#inner_entries: Ghost.erased (list (raw_data_item & raw_data_item)))
  (outer_ml: IT.mixed_list (cbor_map_entry cbor_raw))
  (#pm_outer: perm)
  (#outer_entries: Ghost.erased (list (raw_data_item & raw_data_item)))
: stt (option bool)
    (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
      pm_inner inner_ml inner_entries **
     I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
      pm_outer outer_ml outer_entries **
     pure (
       list_sum (pair_sum raw_data_item_size raw_data_item_size) inner_entries <= Ghost.reveal n /\
       list_sum (pair_sum raw_data_item_size raw_data_item_size) outer_entries <= Ghost.reveal n
     ))
    (fun res ->
      I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
        pm_inner inner_ml inner_entries **
      I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
        pm_outer outer_ml outer_entries **
      pure (res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv inner_entries) outer_entries))
