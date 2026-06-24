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

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_basic_fuel_tagged_case
  (f64: squash SZ.fits_u64)
  (map_bound: option SZ.t)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (compare_rec: compare_cbor_raw_fuel_t basic_data_model (NG.option_sz_v map_bound) (Ghost.hide (Ghost.reveal n - 1)))
  (x1 x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (Tagged? (Ghost.reveal v1) /\ Tagged? (Ghost.reveal v2) /\
        raw_data_item_size v1 <= Ghost.reveal n /\
        raw_data_item_size v2 <= Ghost.reveal n)
returns res: option bool
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (res == check_equiv_tagged_total basic_data_model (NG.option_sz_v map_bound) v1 v2)
{
  cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
  cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
  rewrite (cbor_raw_match_fuel n pm1 x1 v1)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
  rewrite (cbor_raw_match_fuel n pm2 x2 v2)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
  raw_data_item_size_eq v1;
  raw_data_item_size_eq v2;
  cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm1 x1;
  cbor_raw_match_aux_cases (cbor_raw_match_fuel (n - 1)) pm2 x2;
  cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm1 x1;
  cbor_raw_match_aux_fields (cbor_raw_match_fuel (n - 1)) pm2 x2;
  let tag1 = cbor_raw_tag_value x1;
  let tag2 = cbor_raw_tag_value x2;
  cbor_raw_tag_value_eq x1 (Ghost.reveal v1) () ();
  cbor_raw_tag_value_eq x2 (Ghost.reveal v2) () ();
  if (tag1 <> tag2) {
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    Some false
  } else {
    let n1 : Ghost.erased nat = Ghost.hide (Ghost.reveal n - 1);
    let payload1 = cbor_raw_get_tagged_payload_aux (cbor_raw_match_fuel (n - 1)) pm1
                     (cbor_raw_read_fuel n1 pm1 f64) x1 ();
    let payload2 = cbor_raw_get_tagged_payload_aux (cbor_raw_match_fuel (n - 1)) pm2
                     (cbor_raw_read_fuel n1 pm2 f64) x2 ();
    let res = compare_rec payload1 payload2;
    Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
    Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    res
  }
}
```

#pop-options
