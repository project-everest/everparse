module CBOR.Pulse.Raw.EverParse.Nondet.Compare
#lang-pulse
include CBOR.Spec.Raw.Nondet
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
include CBOR.Pulse.Raw.EverParse.Validate
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open LowParse.Spec.VCList
open LowParse.Pulse.VCList
open LowParse.PulseParse.Iterator
open LowParse.PulseParse.VCList
open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice.Util
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module I = LowParse.PulseParse.Iterator
module U64 = FStar.UInt64
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen
module Valid = CBOR.Spec.Raw.Valid

// Callback type: data_model implementation at the cbor_raw level.
// Given two cbor_raw values with cbor_raw_match, returns bool matching data_model on the underlying raw_data_items.
inline_for_extraction
let impl_data_model_t
  (data_model: (raw_data_item -> raw_data_item -> bool))
=
  (x1: cbor_raw) ->
  (x2: cbor_raw) ->
  (#pm1: perm) ->
  (#v1: Ghost.erased raw_data_item) ->
  (#pm2: perm) ->
  (#v2: Ghost.erased raw_data_item) ->
  stt bool
    (cbor_raw_match pm1 x1 v1 **
     cbor_raw_match pm2 x2 v2)
    (fun res ->
      cbor_raw_match pm1 x1 v1 **
      cbor_raw_match pm2 x2 v2 **
      pure (res == data_model v1 v2))

// Wrapper: convert impl_data_model_t (cbor_raw level) to impl_equiv_hd_t (serialized nlist level)
inline_for_extraction
fn impl_data_model_to_equiv_hd
  (#data_model: Ghost.erased (raw_data_item -> raw_data_item -> bool))
  (impl_dm: impl_data_model_t data_model)
  (f64: squash SZ.fits_u64)
: NG.impl_equiv_hd_t data_model
=
  (n1: SZ.t)
  (l1: S.slice byte)
  (n2: SZ.t)
  (l2: S.slice byte)
  (#p1: perm)
  (#gl1: Ghost.erased (nlist (SZ.v n1) raw_data_item))
  (#p2: perm)
  (#gl2: Ghost.erased (nlist (SZ.v n2) raw_data_item))
{
  // === Side 1: extract head as cbor_raw ===

  let hd1 = nlist_hd_strong_prefix () (jump_raw_data_item f64) (SZ.v n1) l1;
  let x1 = cbor_raw_read 1.0R f64 hd1;
  Trade.trans _ _
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1);

  // === Side 2: extract head as cbor_raw ===

  let hd2 = nlist_hd_strong_prefix () (jump_raw_data_item f64) (SZ.v n2) l2;
  let x2 = cbor_raw_read 1.0R f64 hd2;
  Trade.trans _ _
    (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2);

  // === Call data_model callback ===

  let res = impl_dm x1 x2;

  // === Trade back ===

  Trade.elim _ (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n2) parse_raw_data_item) l2 #p2 gl2);
  Trade.elim _ (PPB.pts_to_parsed_strong_prefix (parse_nlist (SZ.v n1) parse_raw_data_item) l1 #p1 gl1);

  res
}
