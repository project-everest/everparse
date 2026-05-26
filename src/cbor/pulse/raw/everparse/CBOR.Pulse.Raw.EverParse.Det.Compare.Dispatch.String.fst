module CBOR.Pulse.Raw.EverParse.Det.Compare.Dispatch.String
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.Compare.Base
open CBOR.Pulse.Raw.Compare.Bytes
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module I16 = FStar.Int16
module Trade = Pulse.Lib.Trade.Util
module NC = CBOR.Pulse.Raw.EverParse.Nondet.Compare

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
```pulse
fn cbor_compare_dispatch_string_case
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (String? (Ghost.reveal v1) /\ String? (Ghost.reveal v2) /\
        String?.typ (Ghost.reveal v1) == String?.typ (Ghost.reveal v2))
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
  let len1 = cbor_raw_string_len x1;
  let len2 = cbor_raw_string_len x2;
  cbor_raw_string_len_eq x1 (Ghost.reveal v1) () ();
  cbor_raw_string_len_eq x2 (Ghost.reveal v2) () ();
  let cl : I16.t = impl_raw_uint64_compare () len1 len2;
  if (cl = 0s) {
    let s1 = cbor_raw_get_string_aux (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
    let s2 = cbor_raw_get_string_aux (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
    let res = lex_compare_bytes s1 s2;
    Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
    Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
    cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
    cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
         as (cbor_raw_match_fuel n pm1 x1 v1);
    rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
         as (cbor_raw_match_fuel n pm2 x2 v2);
    res
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
