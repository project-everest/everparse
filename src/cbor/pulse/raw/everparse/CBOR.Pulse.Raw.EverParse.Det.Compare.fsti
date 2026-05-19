module CBOR.Pulse.Raw.EverParse.Det.Compare
#lang-pulse
include CBOR.Spec.Raw.Format
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.Compare.Base
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module I16 = FStar.Int16

inline_for_extraction
val impl_cbor_compare
  (f64: squash SZ.fits_u64)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm)
  (#v1: Ghost.erased raw_data_item)
  (#pm2: perm)
  (#v2: Ghost.erased raw_data_item)
: stt I16.t
    (cbor_raw_match pm1 x1 v1 **
     cbor_raw_match pm2 x2 v2)
    (fun res ->
      cbor_raw_match pm1 x1 v1 **
      cbor_raw_match pm2 x2 v2 **
      pure (same_sign (I16.v res) (cbor_compare v1 v2)))

