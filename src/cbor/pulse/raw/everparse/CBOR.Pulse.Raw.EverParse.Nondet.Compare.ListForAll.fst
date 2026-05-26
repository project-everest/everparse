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

#push-options "--z3rlimit 512 --fuel 4 --ifuel 4 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_list_for_all_fuel
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
requires
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_inner inner_ml inner_entries **
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_outer outer_ml outer_entries **
  pure (
    list_sum (pair_sum raw_data_item_size raw_data_item_size) inner_entries <= Ghost.reveal n /\
    list_sum (pair_sum raw_data_item_size raw_data_item_size) outer_entries <= Ghost.reveal n
  )
returns res: option bool
ensures
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_inner inner_ml inner_entries **
  I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_outer outer_ml outer_entries **
  pure (res == list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv inner_entries) outer_entries)
{
  let len = IT.mixed_list_length outer_ml;
  I.mixed_list_match_length (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pm_outer outer_ml (Ghost.reveal outer_entries);
  let it_init = I.iterator_start (cbor_map_entry_vmatch_fuel n)
    (nondep_then parse_raw_data_item parse_raw_data_item) jump_nondep_then_raw_data_item_eta pm_outer outer_ml outer_entries
    (cbor_map_entry_vmatch_fuel_share_t n) (cbor_map_entry_vmatch_fuel_gather_t n);
  let mut r_it = it_init;
  let mut r_done : option (option bool) = None #(option bool);
  let mut r_cnt = 0sz;
  while (
    let done = !r_done;
    let cnt = !r_cnt;
    (None? done && SZ.lt cnt len)
  ) invariant exists* it_c done_c cnt_c rem pm_c .
    R.pts_to r_it it_c **
    R.pts_to r_done done_c **
    R.pts_to r_cnt cnt_c **
    I.iterator_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pm_c it_c rem **
    Trade.trade
      (I.iterator_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pm_c it_c rem)
      (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
        pm_outer outer_ml outer_entries) **
    I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
      pm_inner inner_ml inner_entries **
    pure (
      SZ.v cnt_c <= SZ.v len /\
      List.Tot.length rem == SZ.v len - SZ.v cnt_c /\
      list_sum (pair_sum raw_data_item_size raw_data_item_size) rem <=
        list_sum (pair_sum raw_data_item_size raw_data_item_size) outer_entries /\
      list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv inner_entries) outer_entries ==
        (match done_c with
         | Some r -> r
         | None -> list_for_all_with_overflow (setoid_assoc_eq_with_overflow equiv equiv inner_entries) rem)
    )
  {
    let it_cur = !r_it;
    let e, itn = iterator_next_map_entry_raw_data_item_fuel n f64 _ it_cur _;
    r_it := itn;
    with pmv hdv tl pmn . assert (
      cbor_map_entry_vmatch_fuel n pmv e hdv **
      R.pts_to r_it itn **
      I.iterator_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item) pmn itn tl
    );
    Trade.trans _ _
      (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
        pm_outer outer_ml outer_entries);
    let entry_res = compare_cbor_raw_setoid_assoc_eq_fuel n compare_impl f64 inner_ml e;
    match entry_res {
      Some b -> {
        if b {
          Trade.elim_hyp_l _ _
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
              pm_outer outer_ml outer_entries);
          let c = !r_cnt;
          r_cnt := SZ.add c 1sz;
        } else {
          Trade.elim_hyp_l _ _
            (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
              pm_outer outer_ml outer_entries);
          r_done := Some (Some false);
          let c = !r_cnt;
          r_cnt := SZ.add c 1sz;
        }
      }
      None -> {
        Trade.elim_hyp_l _ _
          (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
            pm_outer outer_ml outer_entries);
        r_done := Some (None #bool);
        let c = !r_cnt;
        r_cnt := SZ.add c 1sz;
      }
    }
  };
  Trade.elim _ (I.mixed_list_match (cbor_map_entry_vmatch_fuel n) (nondep_then parse_raw_data_item parse_raw_data_item)
    pm_outer outer_ml outer_entries);
  let done = !r_done;
  match done {
    Some r -> { r }
    None -> { Some true }
  }
}
```

#pop-options
