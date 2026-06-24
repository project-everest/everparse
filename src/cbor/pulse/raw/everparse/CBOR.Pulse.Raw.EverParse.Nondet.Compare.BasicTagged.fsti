module CBOR.Pulse.Raw.EverParse.Nondet.Compare.BasicTagged
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Nondet.Compare.Base
open CBOR.Spec.Util
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module NG = CBOR.Pulse.Raw.EverParse.Nondet.Gen

inline_for_extraction
val compare_cbor_raw_basic_fuel_tagged_case
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (compare_rec: compare_cbor_raw_fuel_t basic_data_model (NG.option_sz_v map_bound) (Ghost.hide (Ghost.reveal n - 1)))
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
: stt (option bool)
    (cbor_raw_match_fuel n pm1 x1 v1 **
     cbor_raw_match_fuel n pm2 x2 v2 **
     pure (Tagged? (Ghost.reveal v1) /\ Tagged? (Ghost.reveal v2) /\
           raw_data_item_size v1 <= Ghost.reveal n /\
           raw_data_item_size v2 <= Ghost.reveal n))
    (fun res ->
      cbor_raw_match_fuel n pm1 x1 v1 **
      cbor_raw_match_fuel n pm2 x2 v2 **
      pure (res == check_equiv_tagged_total basic_data_model (NG.option_sz_v map_bound) v1 v2))
