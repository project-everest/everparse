module CBOR.Pulse.Raw.EverParse.Det.Compare.TaggedCase
#lang-pulse
include CBOR.Pulse.Raw.EverParse.Det.Compare.Base
open CBOR.Spec.Raw.EverParse
open CBOR.Pulse.Raw.EverParse.Type
open CBOR.Pulse.Raw.EverParse.Match
open CBOR.Pulse.Raw.EverParse.Match.Fuel
open CBOR.Pulse.Raw.EverParse.MapEntry.Fuel
open CBOR.Pulse.Raw.EverParse.Access
open CBOR.Pulse.Raw.EverParse.Read
open CBOR.Pulse.Raw.Compare.Base
open CBOR.Pulse.Raw.Compare.Bytes
open LowParse.PulseParse.Iterator
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util
module I16 = FStar.Int16
module PPB = LowParse.PulseParse.Base

#push-options "--z3rlimit 256 --fuel 2 --ifuel 2 --split_queries always"

inline_for_extraction
```pulse
fn compare_cbor_raw_fuel_tagged_case
  (f64: squash SZ.fits_u64)
  (n: Ghost.erased nat { Ghost.reveal n >= 1 })
  (ih: compare_cbor_raw_fuel_t (Ghost.hide (Ghost.reveal n - 1)))
  (x1: cbor_raw)
  (x2: cbor_raw)
  (#pm1: perm) (#v1: Ghost.erased raw_data_item)
  (#pm2: perm) (#v2: Ghost.erased raw_data_item)
requires
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (Tagged? (Ghost.reveal v1) /\ Tagged? (Ghost.reveal v2))
returns res: I16.t
ensures
  cbor_raw_match_fuel n pm1 x1 v1 **
  cbor_raw_match_fuel n pm2 x2 v2 **
  pure (same_sign (I16.v res) (cbor_compare_tagged_total (Ghost.reveal v1) (Ghost.reveal v2)))
{
  // Unfold both fuel-matches to aux
  cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
  cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
  rewrite (cbor_raw_match_fuel n pm1 x1 v1)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
  rewrite (cbor_raw_match_fuel n pm2 x2 v2)
       as (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);

  // Get tagged payloads as elt_or_serialized
  let e1 = cbor_raw_get_tagged_payload_aux_eos (cbor_raw_match_fuel (n - 1)) pm1 x1 ();
  with pm1' payload1 . assert (
    tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm1' e1 payload1 **
    Trade.trade (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm1' e1 payload1)
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
  );
  let e2 = cbor_raw_get_tagged_payload_aux_eos (cbor_raw_match_fuel (n - 1)) pm2 x2 ();
  with pm2' payload2 . assert (
    tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' e2 payload2 **
    Trade.trade (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' e2 payload2)
                (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
  );
  // 4-way dispatch on e1 then e2
  match e1 {
    EElement xx1 -> {
      rewrite (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm1' (EElement xx1) payload1)
           as (cbor_raw_match_fuel (n - 1) pm1' xx1 payload1);
      match e2 {
        EElement xx2 -> {
          rewrite (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' (EElement xx2) payload2)
               as (cbor_raw_match_fuel (n - 1) pm2' xx2 payload2);
          let r = ih xx1 xx2 #pm1' #payload1 #pm2' #payload2;
          rewrite (cbor_raw_match_fuel (n - 1) pm1' xx1 payload1)
               as (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm1' (EElement xx1) payload1);
          rewrite (cbor_raw_match_fuel (n - 1) pm2' xx2 payload2)
               as (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' (EElement xx2) payload2);
          Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
          Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
          cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
          cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
          rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
               as (cbor_raw_match_fuel n pm1 x1 v1);
          rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
               as (cbor_raw_match_fuel n pm2 x2 v2);
          r
        }
        ESerialized s2 -> {
          rewrite (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' (ESerialized s2) payload2)
               as (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #pm2' payload2);
          cbor_raw_match_fuel_implies_pos (n - 1) xx1 #pm1' #payload1;
          let xx2 = cbor_raw_read_fuel (n - 1) pm2' f64 s2 #pm2' #payload2;
          let r = ih xx1 xx2 #pm1' #payload1 #pm2' #payload2;
          Trade.elim (cbor_raw_match_fuel (n - 1) pm2' xx2 payload2)
                     (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #pm2' payload2);
          rewrite (cbor_raw_match_fuel (n - 1) pm1' xx1 payload1)
               as (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm1' (EElement xx1) payload1);
          rewrite (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #pm2' payload2)
               as (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' (ESerialized s2) payload2);
          Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
          Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
          cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
          cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
          rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
               as (cbor_raw_match_fuel n pm1 x1 v1);
          rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
               as (cbor_raw_match_fuel n pm2 x2 v2);
          r
        }
      }
    }
    ESerialized s1 -> {
      rewrite (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm1' (ESerialized s1) payload1)
           as (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #pm1' payload1);
      match e2 {
        EElement xx2 -> {
          rewrite (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' (EElement xx2) payload2)
               as (cbor_raw_match_fuel (n - 1) pm2' xx2 payload2);
          cbor_raw_match_fuel_implies_pos (n - 1) xx2 #pm2' #payload2;
          let xx1 = cbor_raw_read_fuel (n - 1) pm1' f64 s1 #pm1' #payload1;
          let r = ih xx1 xx2 #pm1' #payload1 #pm2' #payload2;
          Trade.elim (cbor_raw_match_fuel (n - 1) pm1' xx1 payload1)
                     (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #pm1' payload1);
          rewrite (cbor_raw_match_fuel (n - 1) pm2' xx2 payload2)
               as (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' (EElement xx2) payload2);
          rewrite (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #pm1' payload1)
               as (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm1' (ESerialized s1) payload1);
          Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
          Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
          cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
          cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
          rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
               as (cbor_raw_match_fuel n pm1 x1 v1);
          rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
               as (cbor_raw_match_fuel n pm2 x2 v2);
          r
        }
        ESerialized s2 -> {
          rewrite (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' (ESerialized s2) payload2)
               as (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #pm2' payload2);
          let r = byte_compare_pts_to_parsed_strong_prefix_data_item f64 s1 s2;
          rewrite (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s1 #pm1' payload1)
               as (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm1' (ESerialized s1) payload1);
          rewrite (PPB.pts_to_parsed_strong_prefix parse_raw_data_item s2 #pm2' payload2)
               as (tagged_payload_eos_match (cbor_raw_match_fuel (n - 1)) pm2' (ESerialized s2) payload2);
          Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1);
          Trade.elim _ (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2);
          cbor_raw_match_fuel_eq_succ n pm1 x1 v1;
          cbor_raw_match_fuel_eq_succ n pm2 x2 v2;
          rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm1 x1 v1)
               as (cbor_raw_match_fuel n pm1 x1 v1);
          rewrite (cbor_raw_match_aux parse_raw_data_item (cbor_raw_match_fuel (n - 1)) pm2 x2 v2)
               as (cbor_raw_match_fuel n pm2 x2 v2);
          r
        }
      }
    }
  }
}
```

#pop-options
