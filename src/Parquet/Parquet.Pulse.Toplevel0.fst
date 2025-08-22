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

assume val validate_is_PAR1 : validate_filter_test_t
  (serialize_seq_flbytes 4)
  is_PAR1

assume val validate_footer : validator parse_footer

module U32 = FStar.UInt32

assume val impl_validate_all 
  (len: U32.t)
  (footer: Ghost.erased (parse_fldata_strong_t serialize_footer (U32.v len)))
  (y: Pulse.Lib.Slice.slice LowParse.Bytes.byte)
  (pm: perm)
:
validate_filter_test_gen_t (pts_to_serialized (serialize_fldata_strong serialize_footer (U32.v len))
      y  #pm
      footer)
  serialize_seq_all_bytes
  (validate_all footer)

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
