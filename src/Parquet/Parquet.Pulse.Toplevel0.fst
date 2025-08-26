module Parquet.Pulse.Toplevel0
#lang-pulse
open Pulse.Lib.Pervasives
open LowParse.Pulse.Combinators
open Parquet.Pulse.Jump
open LowParse.Pulse.SeqBytes
open LowParse.Pulse.Int
open LowParse.Pulse.FLData
include Parquet.Spec.Toplevel

module SZ = FStar.SizeT
module S = Pulse.Lib.Slice.Util
module Trade = Pulse.Lib.Trade.Util
module Rel = CDDL.Pulse.Types.Base
module PV = Parquet.Pulse.Vec
module U64 = FStar.UInt64
module U32 = FStar.UInt32

include Parquet.Pulse.Rel

assume val validate_is_PAR1 : validate_filter_test_t
  (serialize_seq_flbytes 4)
  is_PAR1

assume val validate_footer : validator parse_footer

assume val read_footer : zero_copy_parse rel_file_meta_data serialize_footer

[@@pulse_unfold] noextract
let pts_to_bytes (pm: perm) (x: S.slice byte) (y: bytes) : Tot slprop =
  pts_to x #pm y

assume val impl_validate_file_meta_data (footer_start: SZ.t) : PV.impl_pred emp rel_file_meta_data (validate_file_meta_data (SZ.v footer_start))

assume val impl_validate_all_row_groups (pm: perm) : PV.impl_pred2 emp (pts_to_bytes pm) rel_row_group validate_all_row_groups

let validate_header_magic_number =
  let _ = tot_parse_filter_equiv (tot_parse_seq_flbytes 4) is_PAR1 (parse_seq_flbytes 4) in
  validate_jump_with_offset_and_size_then_parse emp 0sz 4sz (validator_gen_of_validator emp (validate_ext (validate_filter_gen (validate_total_constant_size (parse_seq_flbytes 4) 4sz) (serialize_seq_flbytes 4) is_PAR1 validate_is_PAR1) (parser_of_tot_parser (tot_parse_filter (tot_parse_seq_flbytes 4) is_PAR1))))

fn impl_validate_all0 (pm: perm) : PV.impl_pred2 #_ #_ #_ #_ emp rel_file_meta_data (pts_to_bytes pm) validate_all
=
  (fmd: _)
  (vfmd: _)
  (data: _)
  (vdata: _)
{
  S.pts_to_len data;
  let footer_start = S.len data;
  let res1 = impl_validate_file_meta_data footer_start fmd _;
  if (res1) {
    tot_parse_filter_equiv (tot_parse_seq_flbytes 4) is_PAR1 (parse_seq_flbytes 4);
    let res2 = validate_header_magic_number data vdata;
    if (res2) {
      unfold (rel_file_meta_data fmd vfmd);
      let res = PV.impl_for_all _ _ _ (impl_validate_all_row_groups pm data vdata) fmd.row_groups vfmd.row_groups;
      fold (rel_file_meta_data fmd vfmd);
      res
    } else {
      false
    }
  } else {
    false
  }
}

fn impl_validate_all
  (len: U32.t)
  (footer: Ghost.erased (parse_fldata_strong_t serialize_footer (U32.v len)))
  (y: Pulse.Lib.Slice.slice LowParse.Bytes.byte)
  (pm: perm)
:
validate_filter_test_gen_t (pts_to_serialized (serialize_fldata_strong serialize_footer (U32.v len))
      y  #pm
      footer)
  #_ #_ #_
  serialize_seq_all_bytes
  (validate_all footer)
=
  (x: _)
  (#pm': _)
  (#v: _)
{
  pts_to_serialized_fldata_strong_elim_trade serialize_footer (U32.v len) y;
  let f = read_footer y;
  Trade.trans (rel_file_meta_data _ _) _ _;
  pts_to_serialized_elim_trade serialize_seq_all_bytes x;
  let res = impl_validate_all0 _ f _ x _;
  Trade.elim (pts_to_bytes _ x _) _;
  Trade.elim (rel_file_meta_data _ _) _;
  res
}

let validate_parquet (sq: squash SZ.fits_u32) : validator parse_parquet =
  validate_nondep_then_rtol
    4sz
    (validate_dtuple2_rtol
      4sz
      (leaf_reader_of_reader read_u32_le)
      (fun len -> validate_weaken (dtuple2_rtol_kind parse_seq_all_bytes_kind 0)
        (validate_dtuple2_rtol_gen
          (SZ.uint32_to_sizet len)
          (serialize_fldata_strong serialize_footer (U32.v len))
          (fun footer y pm ->
            (validate_filter_gen'
              (validator_gen_of_validator _ (validate_seq_all_bytes ()))
              serialize_seq_all_bytes
              (validate_all footer)
              (impl_validate_all len footer y pm)
              )
          )
          (validate_fldata_strong
            serialize_footer
            validate_footer
            (SZ.uint32_to_sizet len)
          )
        )
      )
      (validate_total_constant_size parse_u32_le 4sz)
    )
    (validate_filter_gen
      (validate_total_constant_size (parse_seq_flbytes 4) 4sz)
      (serialize_seq_flbytes 4)
      is_PAR1
      validate_is_PAR1
    )
