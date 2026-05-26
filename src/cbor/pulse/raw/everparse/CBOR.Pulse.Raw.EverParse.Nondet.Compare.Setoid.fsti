module CBOR.Pulse.Raw.EverParse.Nondet.Compare.Setoid
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.Base
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open LowParse.PulseParse.Iterator
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I = LowParse.PulseParse.Iterator
module IT = LowParse.PulseParse.Iterator.Type

inline_for_extraction
val compare_cbor_raw_setoid_assoc_eq_fuel
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (#equiv: Ghost.erased (raw_data_item -> raw_data_item -> option bool))
  (compare_impl: compare_cbor_raw_fn_fuel_t n equiv)
  (f64: squash SZ.fits_u64)
  (map_ml: IT.mixed_list (cbor_map_entry cbor_raw))
  (#pm_map: perm)
  (#map_entries: Ghost.erased (list (raw_data_item & raw_data_item)))
  (xr: cbor_map_entry cbor_raw)
  (#pm_xr: perm)
  (#xr_pair: Ghost.erased (raw_data_item & raw_data_item))
: stt (option bool)
    (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
      pm_map map_ml map_entries **
     cbor_map_entry_vmatch_fuel n pm_xr xr xr_pair **
     pure (
       list_sum (pair_sum raw_data_item_size raw_data_item_size) map_entries <= Ghost.reveal n /\
       raw_data_item_size (fst (Ghost.reveal xr_pair)) <= Ghost.reveal n /\
       raw_data_item_size (snd (Ghost.reveal xr_pair)) <= Ghost.reveal n
     ))
    (fun res ->
      I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
        pm_map map_ml map_entries **
      cbor_map_entry_vmatch_fuel n pm_xr xr xr_pair **
      pure (res == setoid_assoc_eq_with_overflow equiv equiv map_entries xr_pair))
