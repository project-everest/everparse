module CBOR.Pulse.Raw.Format.Nondet.Validate
friend CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.Nondet
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Slice
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
#lang-pulse
module EP = CBOR.Pulse.Raw.EverParse.Format
module EPND = CBOR.Pulse.Raw.EverParse.Nondet.Basic

fn cbor_validate_nondet
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
  (pts_to input #pm v)
returns res: SZ.t
ensures
  (pts_to input #pm v ** pure (
    cbor_validate_nondet_post map_key_bound strict_check v res
  ))
{
  let mut poff = 0sz;
  let res = EP.validate_raw_data_item () input poff;
  if (res) {
    let off = !poff;
    let input' = LowParse.Pulse.Base.peek_trade_gen
      CBOR.Spec.Raw.EverParse.serialize_raw_data_item
      input
      0sz
      off;
    with v' . assert (LowParse.Pulse.Base.pts_to_serialized CBOR.Spec.Raw.EverParse.serialize_raw_data_item input' #pm v');
    LowParse.Spec.Base.parser_kind_prop_equiv CBOR.Spec.Raw.EverParse.parse_raw_data_item_kind CBOR.Spec.Raw.EverParse.parse_raw_data_item;
    let res = EPND.impl_check_valid_basic map_key_bound strict_check input';
    Trade.elim _ _;
    CBOR.Spec.Raw.Nondet.check_valid_correct basic_data_model (EPND.option_sz_v map_key_bound) strict_check v';
    if (res) {
      off
    } else {
      0sz
    }
  } else {
    0sz
  }
}

fn cbor_validate_nondet_map_length_bounded
  (map_length_bound: SZ.t)
  (map_key_bound: option SZ.t)
  (strict_check: bool)
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
  (pts_to input #pm v)
returns res: SZ.t
ensures
  (pts_to input #pm v ** pure (
    cbor_validate_nondet_map_length_bounded_post map_length_bound map_key_bound strict_check v res
  ))
{
  LowParse.Spec.Combinators.parse_filter_eq
    CBOR.Spec.Raw.EverParse.parse_raw_data_item
    (CBOR.Spec.Raw.Base.map_length_bounded (SZ.v map_length_bound))
    v;
  let mut poff = 0sz;
  let res = EP.validate_raw_data_item_map_length_bounded map_length_bound input poff;
  if (res) {
    let off = !poff;
    let input' = LowParse.Pulse.Base.peek_trade_gen
      CBOR.Spec.Raw.EverParse.serialize_raw_data_item
      input
      0sz
      off;
    with v' . assert (LowParse.Pulse.Base.pts_to_serialized CBOR.Spec.Raw.EverParse.serialize_raw_data_item input' #pm v');
    LowParse.Spec.Base.parser_kind_prop_equiv CBOR.Spec.Raw.EverParse.parse_raw_data_item_kind CBOR.Spec.Raw.EverParse.parse_raw_data_item;
    let res = EPND.impl_check_valid_basic map_key_bound strict_check input';
    Trade.elim _ _;
    CBOR.Spec.Raw.Nondet.check_valid_correct basic_data_model (EPND.option_sz_v map_key_bound) strict_check v';
    if (res) {
      off
    } else {
      0sz
    }
  } else {
    0sz
  }
}

fn cbor_validate_nondet_bounded
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (input: slice U8.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
requires
  (pts_to input #pm v)
returns res: SZ.t
ensures
  (pts_to input #pm v ** pure (
    cbor_validate_nondet_bounded_post map_depth_bound map_length_bound v res
  ))
{
  LowParse.Spec.Combinators.parse_filter_eq
    CBOR.Spec.Raw.EverParse.parse_raw_data_item
    (CBOR.Spec.Raw.Base.raw_data_item_bounded (SZ.v map_depth_bound) (SZ.v map_length_bound))
    v;
  let mut poff = 0sz;
  let res = EP.validate_raw_data_item_bounded map_depth_bound map_length_bound input poff;
  if (res) {
    let off = !poff;
    let input' = LowParse.Pulse.Base.peek_trade_gen
      CBOR.Spec.Raw.EverParse.serialize_raw_data_item
      input
      0sz
      off;
    with v' . assert (LowParse.Pulse.Base.pts_to_serialized CBOR.Spec.Raw.EverParse.serialize_raw_data_item input' #pm v');
    LowParse.Spec.Base.parser_kind_prop_equiv CBOR.Spec.Raw.EverParse.parse_raw_data_item_kind CBOR.Spec.Raw.EverParse.parse_raw_data_item;
    let res = EPND.impl_check_valid_basic None false input';
    Trade.elim _ _;
    CBOR.Spec.Raw.Nondet.check_valid_correct basic_data_model None false v';
    if (res) {
      off
    } else {
      0sz
    }
  } else {
    0sz
  }
}

let cbor_validate_nondet_bounded_sort_scratch_ok_impl map_depth_bound map_length_bound scratch_len =
  CBOR.Pulse.Raw.EverParse.DupCheck.Top.dupcheck_sort_scratch_ok map_depth_bound map_length_bound scratch_len

fn cbor_validate_nondet_bounded_sort
  (map_depth_bound: SZ.t)
  (map_length_bound: SZ.t)
  (input: slice U8.t)
  (scratch: slice SZ.t)
  (#pm: perm)
  (#v: Ghost.erased (Seq.seq U8.t))
  (#s: Ghost.erased (Seq.seq SZ.t))
requires
  (pts_to input #pm v ** pts_to scratch s)
returns res: SZ.t
ensures
  (pts_to input #pm v ** (exists* s' . pts_to scratch s' ** pure (
    cbor_validate_nondet_bounded_sort_post map_depth_bound map_length_bound (len scratch) v res
  )))
{
  if (not (CBOR.Pulse.Raw.EverParse.DupCheck.Top.dupcheck_sort_scratch_ok map_depth_bound map_length_bound (len scratch))) {
    0sz
  } else {
    LowParse.Spec.Combinators.parse_filter_eq
      CBOR.Spec.Raw.EverParse.parse_raw_data_item
      (CBOR.Spec.Raw.Base.raw_data_item_bounded (SZ.v map_depth_bound) (SZ.v map_length_bound))
      v;
    Seq.slice_length v;
    let mut poff = 0sz;
    let res = EP.validate_raw_data_item_bounded map_depth_bound map_length_bound input poff;
    if (res) {
      let off = !poff;
      let x : Ghost.erased CBOR.Spec.Raw.Base.raw_data_item = Ghost.hide (fst (Some?.v (LowParse.Spec.Base.parse CBOR.Spec.Raw.EverParse.parse_raw_data_item v)));
      let ok = CBOR.Pulse.Raw.EverParse.DupCheck.Top.check_dups_top input map_depth_bound map_length_bound scratch x (Ghost.hide (SZ.v off));
      if (ok) {
        off
      } else {
        0sz
      }
    } else {
      0sz
    }
  }
}
