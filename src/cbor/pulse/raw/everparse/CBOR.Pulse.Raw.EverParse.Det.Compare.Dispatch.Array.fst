module CBOR.Pulse.Raw.EverParse.Det.Compare.Dispatch.Array
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.Compare.Base
open Pulse.Lib.Pervasives

module SZ = FStar.SizeT
module I16 = FStar.Int16
module NC = CBOR.Pulse.Raw.EverParse.Nondet.Compare

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
```pulse
fn cbor_compare_dispatch_array_case
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (ih_array: compare_cbor_raw_fuel_array_local_t n)
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (Array? (Ghost.reveal v1) /\ Array? (Ghost.reveal v2))
returns res: I16.t
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (same_sign (I16.v res) (cbor_compare v1 v2))
{
  cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
  cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
  rewrite (cbor_raw_match_fuel n pm1 x1 v1)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
  rewrite (cbor_raw_match_fuel n pm2 x2 v2)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
  cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm1 x1;
  cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm2 x2;
  NC.cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm1 x1;
  NC.cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm2 x2;
  let len1 = cbor_raw_array_raw_uint64 x1;
  let len2 = cbor_raw_array_raw_uint64 x2;
  cbor_raw_array_raw_uint64_eq x1 (Ghost.reveal v1) () ();
  cbor_raw_array_raw_uint64_eq x2 (Ghost.reveal v2) () ();
  let cl = impl_raw_uint64_compare () len1 len2;
  if (cl = 0s) {
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    let len_sz = SZ.uint64_to_sizet len1.value;
    ih_array () x1 x2 len_sz () #pm1 #v1 #pm2 #v2
  } else {
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    cl
  }
}
```

#pop-options
